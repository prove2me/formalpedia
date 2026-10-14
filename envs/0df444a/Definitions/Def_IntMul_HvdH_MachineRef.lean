-- Prove2me | Definitions.Def_IntMul_HvdH_MachineRef
-- name    : IntMul_HvdH_MachineRef
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T17:25:35.12863+00:00
-- url     : https://prove2.me/theorems/26799e31-acc5-4312-9210-52cc7adad517
-- title:
--   Harvey–van der Hoeven multiplication step as computable list functions
-- statement:
--   Computable list-level reference for one recursive step of the Harvey–van der Hoeven $O(n\log n)$ integer multiplication algorithm, as executed by the multitape machine. Arrays are row-major lists; fixed-point Gaussian integers are pairs $(\mathrm{re},\mathrm{im})\in\mathbb{Z}^2$.
--
--   * `Params` collects the step parameters: $K$ axes, chunk size $b$, number of chunks $L$, target lengths $t_i=2^{e}$ or $2^{e-1}$ (the first `dh` axes), source lengths $s_i$, Gaussian width $\alpha$, working precision $p$ and Fermat-ring digit size $P$.
--   * `fermatW` computes the exact cyclic convolution of two Gaussian arrays on the power-of-two box by packing the last axis into the Fermat ring $\mathbb{Z}/(2^{4rP}+1)$ and running Schönhage–Strassen transforms (`mdif`, `pmulZ`, `mdit`) along the other axes; `convL` rounds it as in `convC_round`.
--   * `FtL` is Bluestein's algorithm around `convL` (approximate DFT on the target box); `fwdL` applies Gaussian resampling $\tilde S$ along every axis, `FtL`, then $\tilde B$ along every axis; `exactConvL` is the list form of `exactConv`.
--   * `refStep q x y` splits $x,y$ into $L$ base-$2^b$ digits, reindexes them onto the source box by the Agarwal–Cooley CRT map, convolves with `exactConvL`, reads the $2L-1$ coefficients back and evaluates them at $2^b$.
--   * `mkParams K N` chooses the parameters for $N$-bit inputs: $b=\lceil\log_2(N+1)\rceil$, $L=\lceil N/b\rceil$, $E=\lceil\log_2 4L\rceil$, $e=\lceil E/K\rceil$, pairwise coprime odd $s_i$ from `copS`, $\alpha = K(\lceil\sqrt{\lceil\sqrt b\rceil}\rceil+2)$, $p = 2b+2E+6K\alpha^2+8\,\mathrm{size}(b)+4K+64$, $P=2p+E+8$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), §5.2–5.3 (Proposition 5.4) with the Bluestein/Fermat-ring variant of Theorem 3.1

import Definitions.Def_IntMul_HvdH_ExactConv
import Definitions.Def_IntMul_HvdH_Fermat

/-!
# The O(n log n) multiplication step as list functions (reference for the machine)

This file fixes, as computable list functions, exactly what the multitape machine computes in one
recursive step of Harvey–van der Hoeven multiplication.  Every array is a row-major list (first axis
outermost).  Fixed-point Gaussian arrays are `List (ℤ × ℤ)`.

* `refStep q x y` is one step: chunking, Agarwal–Cooley reindexing, `exactConvL` (the list form of
  `exactConv` with the DFT oracle `FtL`), inverse reindexing and carrying.
* `FtL` is Bluestein (`fftCa` shape, chirp table `twD`) around `convL`, the exact power-of-two
  convolution done in the Fermat ring `ℤ/(2^{4rP}+1)` by multi-axis FFTs, followed by the rounding
  of `convC_round`.
* The 1-dimensional transforms `difZ` / `ditZ` are those of the Schönhage–Strassen machine.
-/

namespace IntMul.HvdH.Ref

open IntMul.HvdH

/-! ## Generic list helpers -/

/-- Split a list into consecutive pieces of length `n` (the last one may be shorter). -/
def chunkL {α : Type*} (n : ℕ) (L : List α) : List (List α) :=
  (List.range ((L.length + n - 1) / n)).map fun i => (L.drop (i * n)).take n

/-- Transpose an `n × m` row-major list into the `m × n` row-major list. -/
def transposeL {α : Type*} [Inhabited α] (n m : ℕ) (L : List α) : List α :=
  (List.range (m * n)).map fun q => L.getD ((q % n) * m + q / n) default

/-- All indices of the box with sides `dims`, in row-major order; index `l` stands for the
function `i ↦ l.getD i 0`. -/
def boxIdxs : List ℕ → List (List ℕ)
  | [] => [[]]
  | n :: ns => (List.range n).flatMap fun i => (boxIdxs ns).map (i :: ·)

/-- The row-major list of the values of `f` on the box with sides `dims`. -/
def listOf {α : Type*} (dims : List ℕ) (f : (ℕ → ℕ) → α) : List α :=
  (boxIdxs dims).map fun l => f fun i => l.getD i 0

/-- Row-major position of the index `j` in the box with sides `dims`. -/
def rmPos : List ℕ → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | n :: ns, j => j 0 * ns.prod + rmPos ns (fun i => j (i + 1))

/-! ## Tensor products by axis rotation

`tensorGo` applies the maps of `As` to the axes in order: the current first axis (length `n`) is
rotated to the end by a transpose, the map is applied to every contiguous slice of length `n`
(producing slices of length `n'`), and the axis list becomes `rest ++ [n']`.  After all axes
the axes are back in their original order. -/
def tensorGo {α : Type*} [Inhabited α] :
    List (ℕ × (List α → List α)) → List ℕ → List α → List α
  | [], _, L => L
  | (n', A) :: As, n :: rest, L =>
    tensorGo As (rest ++ [n']) ((chunkL n (transposeL n rest.prod L)).flatMap A)
  | _ :: _, [], L => L

/-! ## The one-dimensional resampling maps as list functions -/

/-- `S̃` on a slice of length `s`, producing length `t`. -/
def sapL (p s t α : ℕ) (U : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (List.range t).map (Sapprox p s t α fun j => U.getD j (0, 0))

/-- `B̃` on a slice of length `t`, producing length `s`. -/
def bapL (p s t α : ℕ) (V : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (List.range s).map (Bapprox p s t α fun j => V.getD j (0, 0))

/-! ## The Schönhage–Strassen transforms over `ℤ/F` (copied from the SS machine) -/

/-- Sums of the butterflies. -/
def bflyT (F : ℤ) : List ℤ → List ℤ → List ℤ
  | u :: A, v :: B => ((v + u) % F) :: bflyT F A B
  | _, _ => []

/-- Twisted differences of the butterflies, starting at index `j`. -/
def bflyB (F : ℤ) (E j : ℕ) : List ℤ → List ℤ → List ℤ
  | u :: A, v :: B => (((-v + u) * 2 ^ (j * E)) % F) :: bflyB F E (j + 1) A B
  | _, _ => []

/-- The forward transform (decimation in frequency): input of length `2^j`, root `2^E`, output
in bit-reversed order. -/
def difZ (F : ℤ) : ℕ → ℕ → List ℤ → List ℤ
  | _, 0, A => A
  | E, j + 1, A => difZ F (2 * E) j (bflyT F (A.take (2 ^ j)) (A.drop (2 ^ j))) ++
      difZ F (2 * E) j (bflyB F E 0 (A.take (2 ^ j)) (A.drop (2 ^ j)))

/-- `t_i - 2^(-iE) b_i`, written with `2^(n-iE)` (valid when `2^(2n) ≡ 1`). -/
def dcomX (F : ℤ) (n E i : ℕ) : List ℤ → List ℤ → List ℤ
  | t :: T, b :: B => ((t + -((b * 2 ^ (n - i * E)) % F)) % F) :: dcomX F n E (i + 1) T B
  | _, _ => []

def dcomY (F : ℤ) (n E i : ℕ) : List ℤ → List ℤ → List ℤ
  | t :: T, b :: B => ((t + (b * 2 ^ (n - i * E)) % F) % F) :: dcomY F n E (i + 1) T B
  | _, _ => []

/-- The inverse transform (decimation in time), input in the output order of `difZ`; over
`F = 2^n + 1` it inverts `difZ` up to the factor `2^j`. -/
def ditZ (F : ℤ) (n : ℕ) : ℕ → ℕ → List ℤ → List ℤ
  | _, 0, B => B
  | E, j + 1, B =>
    dcomX F n E 0 (ditZ F n (2 * E) j (B.take (2 ^ j))) (ditZ F n (2 * E) j (B.drop (2 ^ j))) ++
      dcomY F n E 0 (ditZ F n (2 * E) j (B.take (2 ^ j))) (ditZ F n (2 * E) j (B.drop (2 ^ j)))

/-- Pointwise products, reduced mod `F`. -/
def pmulZ (F : ℤ) : List ℤ → List ℤ → List ℤ
  | a :: A, b :: B => (a * b) % F :: pmulZ F A B
  | _, _ => []

/-! ## Multi-axis transforms

An array over the outer box `2^{j_0} × ⋯ × 2^{j_{m-1}}` is a row-major `List ℤ`.  Axis `0` is
transformed column by column (a column is one entry of every block of size `B = 2^{j_1+⋯}`),
then every block recursively.  `axes` lists the pairs `(j_i, E_i)`. -/

/-- Apply `f` to each of the `B` columns of `2^j` blocks of size `B`. -/
def colMap (j B : ℕ) (f : List ℤ → List ℤ) (A : List ℤ) : List ℤ :=
  transposeL B (2 ^ j) ((chunkL (2 ^ j) (transposeL (2 ^ j) B A)).flatMap f)

def blockSize (axes : List (ℕ × ℕ)) : ℕ := 2 ^ (axes.map Prod.fst).sum

def mdif (F : ℤ) : List (ℕ × ℕ) → List ℤ → List ℤ
  | [], A => A
  | (j, E) :: rest, A =>
    (chunkL (blockSize rest) (colMap j (blockSize rest) (difZ F E j) A)).flatMap (mdif F rest)

def mdit (F : ℤ) (n : ℕ) : List (ℕ × ℕ) → List ℤ → List ℤ
  | [], A => A
  | (j, E) :: rest, A =>
    colMap j (blockSize rest) (ditZ F n E j)
      ((chunkL (blockSize rest) A).flatMap (mdit F n rest))

/-! ## Parameters -/

/-- The parameters of one step. Axis `i < K` has target length `t i` (a power of two; the last
axis has the full length `r = 2^e`) and source length `s i`. -/
structure Params where
  /-- number of axes (`d + 1` in `bluestein_fp`) -/
  K : ℕ
  /-- chunk size in bits -/
  b : ℕ
  /-- number of chunks of each input -/
  L : ℕ
  /-- `r = 2^e` -/
  e : ℕ
  /-- the first `dh` axes have target length `r/2`, the others `r` -/
  dh : ℕ
  /-- source lengths, `s.length = K` -/
  s : List ℕ
  α : ℕ
  /-- fixed-point precision -/
  p : ℕ
  /-- digit size of the Fermat ring `2^{4rP}+1` -/
  P : ℕ

namespace Params

variable (q : Params)

def r : ℕ := 2 ^ q.e

/-- `log₂` of the target length of axis `i`. -/
def te (i : ℕ) : ℕ := if i < q.dh then q.e - 1 else q.e

/-- target lengths (all axes) -/
def tdims : List ℕ := (List.range q.K).map fun i => 2 ^ q.te i

/-- source lengths -/
def sdims : List ℕ := q.s

/-- `log₂ T` with `T = ∏ tᵢ`. -/
def logT : ℕ := ((List.range q.K).map q.te).sum

/-- `S = ∏ sᵢ` -/
def S : ℕ := q.s.prod

/-- The Fermat exponent `n = 4rP`; the ring is `ℤ/(2^n+1)`. -/
def fn : ℕ := 4 * q.r * q.P

def F : ℤ := 2 ^ q.fn + 1

/-- The outer axes `0, …, K-2` with their transform roots: `(jᵢ, Eᵢ)` with `2^{jᵢ} Eᵢ = 2n`. -/
def outerAxes : List (ℕ × ℕ) :=
  (List.range (q.K - 1)).map fun i => (q.te i, 2 * q.fn / 2 ^ q.te i)

/-- `log₂` of the number of outer positions. -/
def logOuter : ℕ := ((List.range (q.K - 1)).map q.te).sum

end Params

/-! ## The exact convolution in the Fermat ring -/

/-- Encode one block of `r` Gaussian integers (the last axis) as
`∑ re_c y^c + ∑ im_c y^{c+2r}` at `y = 2^P`. -/
def encBlk (P r : ℕ) (blk : List (ℤ × ℤ)) : ℤ :=
  kpack (2 ^ P) (blk.map Prod.fst ++ List.replicate r 0 ++ blk.map Prod.snd)

/-- Decode one Fermat residue to `r` Gaussian integers: balanced residue, `4r` balanced digits,
then fold `y^{c+r} ↦ y^c` (`y^r = 1` on the last axis) and `y^{2r} ↦ i`. -/
def decBlk (F : ℤ) (P r : ℕ) (z : ℤ) : List (ℤ × ℤ) :=
  let dg := kunpack (2 ^ P) (4 * r) (balMod F z)
  (List.range r).map fun c =>
    (dg.getD c 0 + dg.getD (c + r) 0, dg.getD (2 * r + c) 0 + dg.getD (3 * r + c) 0)

/-- The exact cyclic convolution `W` of two Gaussian arrays over the target box (claimed: equal
to `∑_k U_k V_{j-k}` when the entries are in the disc of radius `2^p` and `P` is large). -/
def fermatW (q : Params) (U V : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  let F := q.F
  let encA := (chunkL q.r U).map fun blk => encBlk q.P q.r blk % F
  let encB := (chunkL q.r V).map fun blk => encBlk q.P q.r blk % F
  let C := mdit F q.fn q.outerAxes (pmulZ F (mdif F q.outerAxes encA) (mdif F q.outerAxes encB))
  -- divide by `2^{logOuter}` using `2^{2n} ≡ 1 (mod F)`
  let C' := C.map fun z => (z * 2 ^ (2 * q.fn - q.logOuter)) % F
  C'.flatMap (decBlk F q.P q.r)

/-- The convolution oracle of `bluestein_fp` (rounding of `convC_round`). -/
def convL (q : Params) (U V : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (fermatW q U V).map fun w =>
    (w.1.tdiv ((2 ^ (q.p + q.logT) : ℕ) : ℤ), w.2.tdiv ((2 ^ (q.p + q.logT) : ℕ) : ℤ))

/-- Bluestein's chirp index `∑_{i<K-1} (r/tᵢ) jᵢ² + j_{K-1}²` (the `chirpIdx` of `ConvC`). -/
def chirpIdxL (q : Params) (j : ℕ → ℕ) : ℕ :=
  ((List.range (q.K - 1)).map fun i => q.r / 2 ^ q.te i * j i ^ 2).sum + j (q.K - 1) ^ 2

/-- The chirp table `ãⱼ = twD p (2r) (chirpIdx j)` over the target box. -/
def chirpL (q : Params) : List (ℤ × ℤ) :=
  listOf q.tdims fun j => twD q.p (2 * q.r) (chirpIdxL q j)

/-- The DFT oracle on the target box: Bluestein around `convL` (the shape of `fftCa`). -/
def FtL (q : Params) (U : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  let A := chirpL q
  List.zipWith (fun a z => mulZ q.p (conjZ a) z) A
    (convL q (List.zipWith (fun a u => mulZ q.p (conjZ a) u) A U) A)

/-! ## The approximate DFT on the source box and the exact convolution -/

/-- `fwdZ` as a list function: `S̃` along every axis, the oracle, `B̃` along every axis. -/
def fwdL (q : Params) (U : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  let axS := (List.range q.K).map fun i =>
    (2 ^ q.te i, sapL q.p (q.s.getD i 1) (2 ^ q.te i) q.α)
  let axB := (List.range q.K).map fun i =>
    (q.s.getD i 1, bapL q.p (q.s.getD i 1) (2 ^ q.te i) q.α)
  tensorGo axB q.tdims (FtL q (tensorGo axS q.sdims U))

/-- `exactConv` as a list function over the source box. -/
def exactConvL (q : Params) (u v : List ℤ) : List ℤ :=
  let U := u.map fun a => (a * 2 ^ (q.p - q.b), (0 : ℤ))
  let V := v.map fun a => (a * 2 ^ (q.p - q.b), (0 : ℤ))
  let Ua := fwdL q U
  let Va := fwdL q V
  let W := List.zipWith (fun a b => conjZ (mulZ q.p a b)) Ua Va
  let Y := fwdL q W
  Y.map fun z => roundDiv (z.1 * (q.S : ℤ) ^ 2 * 2 ^ (2 * q.b + 6 * q.K * q.α ^ 2)) (2 ^ q.p)

/-! ## Chunking and Agarwal–Cooley reindexing -/

/-- The `L` base-`2^b` digits of `x`, least significant first. -/
def chunksL (b L x : ℕ) : List ℤ := (List.range L).map fun k => ((x / 2 ^ (b * k) % 2 ^ b : ℕ) : ℤ)

/-- CRT coefficient `cᵢ = (S/sᵢ) · ((S/sᵢ)⁻¹ mod sᵢ)`: `cᵢ ≡ 1 (mod sᵢ)`, `≡ 0 (mod sⱼ)`. -/
def crtCoef (s : List ℕ) (i : ℕ) : ℕ :=
  s.prod / s.getD i 1 * (((s.prod / s.getD i 1 : ℕ) : ZMod (s.getD i 1))⁻¹).val

/-- The position `k < S` with `k ≡ jᵢ (mod sᵢ)` for all `i`. -/
def crtIdx (s : List ℕ) (j : ℕ → ℕ) : ℕ :=
  ((List.range s.length).map fun i => j i * crtCoef s i).sum % s.prod

/-- Reindex a digit sequence onto the source box. -/
def crtIn (s : List ℕ) (c : List ℤ) : List ℤ := listOf s fun j => c.getD (crtIdx s j) 0

/-- Read the first `M` coefficients back from the source box: `cₖ = w_{(k mod sᵢ)ᵢ}`. -/
def crtOut (s : List ℕ) (M : ℕ) (w : List ℤ) : List ℤ :=
  (List.range M).map fun k => w.getD (rmPos s fun i => k % s.getD i 1) 0

/-- `∑ cₖ 2^{bk}`. -/
def evalDigits (b : ℕ) (c : List ℤ) : ℤ :=
  ((List.range c.length).map fun k => c.getD k 0 * 2 ^ (b * k)).sum

/-- One recursive step: the product of `x, y < 2^{bL}`. -/
def refStep (q : Params) (x y : ℕ) : ℤ :=
  let u := crtIn q.s (chunksL q.b q.L x)
  let v := crtIn q.s (chunksL q.b q.L y)
  evalDigits q.b (crtOut q.s (2 * q.L - 1) (exactConvL q u v))

end IntMul.HvdH.Ref

namespace IntMul.HvdH.Ref

open IntMul.HvdH

/-! ## The parameter choice

`K` axes; chunks of `b = size N` bits; `T = 2^E ≥ 4L`; `r = 2^e` with `e = ⌈E/K⌉`, the first
`dh = Ke - E` axes of target length `r/2`; source lengths from the construction of
`coprime_params` (pairwise coprime, odd, `(1-2η)tᵢ < sᵢ ≤ (1-η)tᵢ`, `η = 1/(4K)`). -/

/-- The modulus `Q` of the `coprime_params` construction. -/
def copQ (K r : ℕ) : ℕ :=
  2 * (256 * K ^ 2).factorial * (r / (2 * (256 * K ^ 2).factorial * (256 * K ^ 2)) + 1)

/-- The source lengths `sᵢ = 1 + Q mᵢ` of the `coprime_params` construction. -/
def copS (K dh r : ℕ) : List ℕ :=
  let Q := copQ K r
  let m1 := ((4 * K - 1) * (r / 2) - 4 * K) / (4 * K * Q)
  let m2 := ((4 * K - 1) * r - 4 * K) / (4 * K * Q)
  (List.range K).map fun i => 1 + Q * (if i < dh then m1 - i else m2 - (i - dh))

/-- The parameters for inputs of `N` bits. -/
def mkParams (K N : ℕ) : Params :=
  let b := Nat.size N
  let L := (N + b - 1) / b
  let E := Nat.clog 2 (4 * L)
  let e := (E + K - 1) / K
  let dh := K * e - E
  let α := K * (ceilSqrt (ceilSqrt b) + 2)
  let p := 2 * b + 2 * E + 6 * K * α ^ 2 + 8 * Nat.size b + 4 * K + 64
  { K := K, b := b, L := L, e := e, dh := dh, s := copS K dh (2 ^ e), α := α, p := p,
    P := 2 * p + E + 8 }

end IntMul.HvdH.Ref


