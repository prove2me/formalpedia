-- Prove2me | Definitions.Def_FineGrainedEF_Main_FFTMul
-- name    : FineGrainedEF_Main_FFTMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:11:42.295196+00:00
-- url     : https://prove2.me/theorems/6ae5e419-7f57-4283-9326-dbc3a77eb5a8
-- title:
--   The FFT multiplier of A.4–A.5: parameters N, L, p, t, roots (44)–(45), twiddles (46), FFT, IFFT, FFTConv and FFTMul
-- statement:
--   **Parameters** (p. 48). For input length $n$: $N=2^{\lceil\log_2(16(n+1))\rceil}$, $L=\log_2N$, $p=1024(L+1)^2$, $t=Lp$; $w_q=t+3L+2$, $\Delta w=w_q+3$. They are fixed by the theorem's $n$ for the whole joint computation, nested products included (p. 53).
--
--   **Roots** (p. 49). Numerators at scale $p$: $z_1:=\mathrm{Prmt}_p(-1)$, $z_2:=\mathrm{Prmt}_p(i)$, and for $s\ge2$, if $z_s=(A+iB)2^{-p}$ then $z_{s+1}=(U+iV)2^{-p}$ with $U,V\in[0,2^p]$ the largest integers satisfying
--   $$U^2\le(2^p+A)\,2^{p-1},\qquad 2UV\le B\,2^p,$$
--   which are the inequalities (44) $u^2\le\mathrm{Prmt}_{2p}((\mathrm{Prmt}_p(1)+_pa)/2)<(u+_ph)^2$ and (45) $2uv\le\mathrm{Prmt}_{2p}(b)<2u(v+_ph)$ for $u=U2^{-p}$, $v=V2^{-p}$, $h=2^{-p}$.
--
--   **Twiddles** (46). For $m=2^s$ and address $a=\sum_{r<s}2^ra_r$ (modulo $m$), $q_m(a):=\mathrm{Prmt}_t\big(\prod_{r<s}z_{s-r}^{a_r}\big)$, the exact product with $z^0:=\mathrm{Prmt}_p(1)$, hardwired in $C_{t,w_q}$; $q_1(0)=\mathrm{Prmt}_t(1)$. The conjugate $\bar q_m(a)$ is hardwired at width $w_q+1$.
--
--   **Networks** (A.5.1–A.5.3). $\mathrm{FFT}_1(v)=v$; $\mathrm{FFT}_m(v)_a:=\mathrm{Add}_k(\mathrm{Prmt}_k(E_b),\mathrm{Mul}_{t,f}(q_m(a),O_b))$ with $E,O$ the transforms of the even and odd entries, $b=a\bmod m/2$, $k=f+t$; outputs sign-extended to $w+\Delta w$, with the promoted even-child word shared by both outputs of each butterfly pair. $\mathrm{IFFT}^{\mathrm{raw}}_m$: $s_a:=\mathrm{Prmt}_{f+t}(\mathrm{Add}_f(v_a,v_{a+m/2}))$, $r_a:=\mathrm{Mul}_{t,f}(\bar q_m(a),\mathrm{Sub}_f(v_a,v_{a+m/2}))$, sign-extended to $w+\Delta w$, then the transforms of $s$ and $r$ interleaved; $\mathrm{IFFT}(v):=N^{-1}\mathrm{IFFT}^{\mathrm{raw}}_N(v)$ (scale $+L$).
--
--   **Multiplier** (p. 50). $\mathrm{FFTConv}_{\mathrm{raw}}(a,b):=\mathrm{IFFT}(\mathrm{FFT}(a)\odot\mathrm{FFT}(b))$, $\mathrm{FFTConv}_{\mathrm{round}}(a,b)_j:=\mathrm{Round}(\mathrm{Re}\,\mathrm{FFTConv}_{\mathrm{raw}}(a,b)_j)$ on real arrays embedded as $x+i0$. For unsigned $x\in\{0,1\}^r$, $y\in\{0,1\}^s$, the bit embeddings $a,b$ have entry $x_j$ (resp. $y_j$) as a two-bit scale-zero numerator for $j<r$ (resp. $s$) and zero elsewhere, and
--   $$\mathrm{FFTMul}_{r,s}(x,y):=\big(\mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(a,b))_j\big)_{0\le j<\ell},\qquad \ell=r+s+L+2.$$
--
--   **Formalization Note.** `FFTParams`, `paperParams`, `wq`, `dw`, `rootNum` (via `Nat.findGreatest` over $[0,2^p]$), `gmul`, `twiddleNum`, `twiddle`, `twiddleConj`, `fft`, `ifftRaw`, `ifft`, `fftConvRaw`, `fftConvRound`, `fftConvRoundInt`, `bitEmbed`, `fftMulFull` (all $N$ carry bits and the carries), `fftMul`. Every arithmetic operation keeps its full result; arrays are sign-extended to a common width before the transforms (p. 45).
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 48-53, §A.4-A.5 (parameters p. 48; roots (44)-(45) and twiddles (46) p. 49; A.5 pp. 50-52; widths p. 53)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith

namespace FineGrainedEF.Main

/-- The four global FFT parameters (p. 48): transform length `N`, number of levels `L`, root
precision `p` and twiddle scale `t`. -/
structure FFTParams where
  N : ℕ
  L : ℕ
  p : ℕ
  t : ℕ

/-- The paper's parameters for input length `n` (p. 48):
`N = 2^{⌈log(16(n+1))⌉}`, `L = log N`, `p = 1024 (L+1)^2`, `t = L p` (logarithms base two). They
are fixed by the theorem's `n` for the whole joint computation, nested products included (p. 53). -/
def paperParams (n : ℕ) : FFTParams :=
  let L := Nat.clog 2 (16 * (n + 1))
  ⟨2 ^ L, L, 1024 * (L + 1) ^ 2, L * (1024 * (L + 1) ^ 2)⟩

/-- Twiddle component width `w_q = t + 3L + 2` (p. 49). -/
def FFTParams.wq (P : FFTParams) : ℕ := P.t + 3 * P.L + 2

/-- Butterfly width increment `∆w = w_q + 3` (p. 51). -/
def FFTParams.dw (P : FFTParams) : ℕ := P.wq + 3

/-- Numerators (at scale `p`) of the hardwired roots `z_s ∈ C_{p, p+2}` (p. 49):
`z_1 := Prmt_p(-1)`, `z_2 := Prmt_p(i)`, and for `s ≥ 2`, with `z_s = (A + iB) 2^{-p}`,
`z_{s+1} := (U + iV) 2^{-p}` where `U, V ∈ [0, 2^p]` are the largest numerators with
`U^2 ≤ (2^p + A) 2^{p-1}` and `2 U V ≤ B 2^p`, i.e. (44) `u² ≤ Prmt_{2p}((Prmt_p(1) +_p a)/2)` and
(45) `2uv ≤ Prmt_{2p}(b)` with `u = U h`, `v = V h`, `h = 2^{-p}`. (Index `0` is unused.) -/
def rootNum (p : ℕ) : ℕ → ℤ × ℤ
  | 0 => (2 ^ p, 0)
  | 1 => (-(2 ^ p), 0)
  | 2 => (0, 2 ^ p)
  | s + 3 =>
      let z := rootNum p (s + 2)
      let X : ℤ := (2 ^ p + z.1) * 2 ^ (p - 1)
      let U : ℕ := Nat.findGreatest (fun U : ℕ => (U : ℤ) ^ 2 ≤ X) (2 ^ p)
      let V : ℕ := Nat.findGreatest (fun V : ℕ => 2 * (U : ℤ) * V ≤ z.2 * 2 ^ p) (2 ^ p)
      ((U : ℤ), (V : ℤ))

/-- Gaussian-integer product (complex product of numerators). -/
def gmul (x y : ℤ × ℤ) : ℤ × ℤ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Numerators at scale `t` of the twiddle `q_m(a)`, `m = 2^s` (46), p. 49:
`q_m(a) := Prmt_t(∏_{r<s} z_{s-r}^{a_r})`, the exact product, where the address bit `a_r = 1`
selects `z_{s-r}` and `a_r = 0` selects `z^0_{s-r} := Prmt_p(1)`; the product has scale `s p` and
is promoted to scale `t`. Addresses are taken modulo `m`. For `s = 0` this is `q_1(0) = Prmt_t(1)`. -/
def twiddleNum (P : FFTParams) (s a : ℕ) : ℤ × ℤ :=
  let prod := (List.range s).foldl
    (fun acc r => gmul acc (if (a % 2 ^ s).testBit r then rootNum P.p (s - r) else (2 ^ P.p, 0)))
    (1, 0)
  (prod.1 * 2 ^ (P.t - s * P.p), prod.2 * 2 ^ (P.t - s * P.p))

/-- The hardwired twiddle `q_m(a) ∈ C_{t, w_q}`, `m = 2^s`. -/
def twiddle (P : FFTParams) (s a : ℕ) : Build SCpx :=
  cpxConst (twiddleNum P s a) P.t P.wq

/-- The hardwired conjugate twiddle `q̄_m(a)` (p. 52), at scale `t`; conjugation adds one bit
(width `w_q + 1`, p. 53). -/
def twiddleConj (P : FFTParams) (s a : ℕ) : Build SCpx :=
  let q := twiddleNum P s a
  cpxConst (q.1, -q.2) P.t (P.wq + 1)

/-- Even-indexed entries `v^e_j = v_{2j}`. -/
def evens {α : Type} [Inhabited α] (v : List α) : List α :=
  (List.range (v.length / 2)).map fun j => v.getD (2 * j) default

/-- Odd-indexed entries `v^o_j = v_{2j+1}`. -/
def odds {α : Type} [Inhabited α] (v : List α) : List α :=
  (List.range (v.length / 2)).map fun j => v.getD (2 * j + 1) default

/-- Interleaving `(E_0, O_0, E_1, O_1, …)`. -/
def interleave {α : Type} : List α → List α → List α
  | e :: es, o :: os => e :: o :: interleave es os
  | _, _ => []

/-- The forward network `FFT_m`, `m = 2^s` (A.5.1, p. 51): `FFT_1(v) := v`; for `m ≥ 2`,
`E := FFT_{m/2}(v^e)`, `O := FFT_{m/2}(v^o)`, and for each output `a < m`, with
`b := a mod (m/2)`, `k = f + t` (`f` the scale of the children's outputs),
`(FFT_m(v))_a := Add_k(Prmt_k(E_b), Mul_{t,f}(q_m(a), O_b))`; both outputs of a butterfly are
sign-extended to `w + ∆w` (`w` the children's component width, A.5.4). -/
def fft (P : FFTParams) : ℕ → List SCpx → Build (List SCpx)
  | 0, v => pure v
  | s + 1, v => do
      let E ← fft P s (evens v)
      let O ← fft P s (odds v)
      let w := max ((E.headD default).width) ((O.headD default).width)
      -- The two outputs in each butterfly share the promoted even-child word (p. 52).
      let promoted ← E.mapM fun e => e.prmt (e.sc + P.t)
      (List.range (2 ^ (s + 1))).mapM fun a => do
        let b := a % 2 ^ s
        let e' := promoted.getD b default
        let Ob := O.getD b default
        let q ← twiddle P (s + 1) a
        let pr ← SCpx.mul q Ob
        let out ← SCpx.add e' pr
        out.signExt (w + P.dw)

/-- The unnormalized inverse network `IFFT^raw_m`, `m = 2^s` (A.5.3, p. 52): for `m ≥ 2` and
`a < m/2`, `s_a := Prmt_{f+t}(Add_f(v_a, v_{a+m/2}))`,
`r_a := Mul_{t,f}(q̄_m(a), Sub_f(v_a, v_{a+m/2}))`, both sign-extended to `w + ∆w`; then
`E := IFFT^raw_{m/2}(s)`, `O := IFFT^raw_{m/2}(r)`, output `(E_0, O_0, E_1, O_1, …)`. -/
def ifftRaw (P : FFTParams) : ℕ → List SCpx → Build (List SCpx)
  | 0, v => pure v
  | s + 1, v => do
      let w := (v.headD default).width
      let pairs ← (List.range (2 ^ s)).mapM fun a => do
        let va := v.getD a default
        let vb := v.getD (a + 2 ^ s) default
        let sm ← SCpx.add va vb
        let sa ← sm.prmt (va.sc + P.t)
        let df ← SCpx.sub va vb
        let qc ← twiddleConj P (s + 1) a
        let ra ← SCpx.mul qc df
        let sa' ← sa.signExt (w + P.dw)
        let ra' ← ra.signExt (w + P.dw)
        pure (sa', ra')
      let E ← ifftRaw P s (pairs.map Prod.fst)
      let O ← ifftRaw P s (pairs.map Prod.snd)
      pure (interleave E O)

/-- `IFFT(v) := N^{-1} IFFT^raw_N(v)` (p. 52): the division by `N = 2^L` is the exact scale change
`+L`. -/
def ifft (P : FFTParams) (v : List SCpx) : Build (List SCpx) := do
  let r ← ifftRaw P P.L v
  pure (r.map (SCpx.divPow2 P.L))

/-- `FFTConv_raw(a, b) := IFFT(FFT(a) ⊙ FFT(b))` (p. 50) on length-`N` complex arrays, after
sign-extending each array to its common component width (p. 45); `⊙` is the entrywise complex
`Mul` (A.5.2). -/
def fftConvRaw (P : FFTParams) (a b : List SCpx) : Build (List SCpx) := do
  let wa := (a.map SCpx.width).foldl max 0
  let wb := (b.map SCpx.width).foldl max 0
  let a' ← a.mapM (SCpx.signExt wa)
  let b' ← b.mapM (SCpx.signExt wb)
  let fa ← fft P P.L a'
  let fb ← fft P P.L b'
  let pr ← (List.zip fa fb).mapM fun x => SCpx.mul x.1 x.2
  ifft P pr

/-- `FFTConv_round(a, b)_j := Round(Re FFTConv_raw(a, b)_j)` (p. 50) for real arrays `a, b` of
length `N` (embedded as `x + i0`, p. 47); returns the scale-zero integer numerators. -/
def fftConvRound (P : FFTParams) (a b : List SReal) : Build (List (List ℕ)) := do
  let ea ← a.mapM SReal.embed
  let eb ← b.mapM SReal.embed
  let raw ← fftConvRaw P ea eb
  let r ← raw.mapM fun c => SReal.round ⟨c.re, c.sc⟩
  pure (r.map SReal.num)

/-- `FFTConv_round` on scale-zero integer coefficient arrays (`D_0^N`). -/
def fftConvRoundInt (P : FFTParams) (a b : List (List ℕ)) : Build (List (List ℕ)) :=
  fftConvRound P (a.map fun x => ⟨x, 0⟩) (b.map fun x => ⟨x, 0⟩)

/-- Bit embedding of an unsigned binary input (p. 50): length-`N` array of scale-zero real
coefficients; entry `j < |x|` is bit `x_j` zero-extended to a two-bit signed numerator, every other
entry the two-bit zero (all hardwired zeros are one fresh constant). -/
def bitEmbed (N : ℕ) (x : List ℕ) : Build (List (List ℕ)) := do
  let z ← zeroG
  pure ((List.range N).map fun j => if j < x.length then [x.getD j 0, z] else [z, z])

/-- The full multiplier pipeline `Carry(FFTConv_round(a, b))` on the bit embeddings `a, b` of `x, y`:
all `N` output bits and the carries `κ_0, …, κ_N`. -/
def fftMulFull (P : FFTParams) (x y : List ℕ) : Build (List ℕ × List (List ℕ)) := do
  let a ← bitEmbed P.N x
  let b ← bitEmbed P.N y
  let c ← fftConvRoundInt P a b
  carry c

/-- `FFTMul_{r,s}(x, y) := (Carry(FFTConv_round(a, b))_j)_{0 ≤ j < ℓ}`, `ℓ = r + s + L + 2`
(A.5, p. 50), with `r = |x|`, `s = |y|` and the global parameters `P`. -/
def fftMul (P : FFTParams) (x y : List ℕ) : Build (List ℕ) := do
  let r ← fftMulFull P x y
  pure (r.1.take (x.length + y.length + P.L + 2))

end FineGrainedEF.Main


