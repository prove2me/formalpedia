-- Prove2me | Definitions.Def_KXorTPCA_Reduction_Models
-- name    : KXorTPCA_Reduction_Models
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:20:12.378385+00:00
-- url     : https://prove2.me/theorems/4dc4a624-0aa5-429e-9ca0-33a3050d67cd
-- title:
--   Planted and null k-XOR / k-Gauss model family (Definition 6.1, Fig. 6, Definitions A.1, C.1) and k-Tensor PCA (Eq. (2), (19))
-- statement:
--   A **planted problem** at signal dimension $n$ is a pair of samplers, from one pair of random tapes, of the **null** instance and, for each secret $x\in\{\pm1\}^n$, of the **planted** instance $P_x$; instances are encoded as memory images. A **family** assigns a planted problem to each parameter pair and dimension.
--
--   **The model family of Fig. 6.** Fix the order $k$, the dimension $n$, a sample parameter $m\ge0$ and a signal level $\delta$. Write $\mathrm{Rad}(\delta)$ for the $\pm1$ variable with $\mathbb E[\mathrm{Rad}(\delta)]=\delta$ and $x_\alpha=\prod_{i\in\alpha}x_i$ (with multiplicity). Four choices:
--
--   1. noise: **k-XOR** $Y_j=s_j\cdot W_j$, $W_j\sim\mathrm{Rad}(\delta)$; or **k-Gauss** $Y_j=\delta s_j+G_j$, $G_j\sim N(0,1)$;
--   2. number of samples: $\lfloor m\rfloor$; or $\mathrm{Pois}(m)$ (**Pois**);
--   3. index space: $k$-sets of distinct indices of $[n]$; or $k$-multisets with the measure $\mu(\{i_1,\dots,i_k\})\propto\#\{(j_1,\dots,j_k)\in[n]^k:\{j_1,\dots,j_k\}=\{i_1,\dots,i_k\}\}$ of Definition A.1 (**FULL**); or ordered $k$-tuples of distinct indices (**asymm**);
--   4. sampling: $\alpha_j$ i.i.d. (with replacement); or (**wor**) the first $\min(\text{count},\#\text{index objects})$ index objects in a random order in which each next object is drawn from the remaining ones with probability proportional to the index space's measure (uniform for $k$-sets and ordered tuples, $\mu$ of Definition A.1 for FULL).
--
--   In the planted instance $s_j=x_{\alpha_j}$; in the null instance (Definition C.1) $s_j=w_j$, independent uniform signs. All draws are independent. The **(ρ, η) parametrization** (§3, Definition 1.1) sets
--
--   $$m=n^{k(1+\rho)/2},\qquad \delta=n^{-k\rho/4-\eta/2}.$$
--
--   **Tensor PCA** $k$-TensorPCA$(N,\delta)$ (Eq. (2), (19)): one observes the whole array $Y\in\mathbb R^{[N]^k}$ with
--
--   $$Y_{i_1\dots i_k}=\delta\, s_{i_1\dots i_k}+G_{\{i_1,\dots,i_k\}},$$
--
--   one independent $G_\beta\sim N(0,1)$ per $k$-multiset $\beta$ ("$G$ is a symmetric tensor of $N(0,1)$"), $s=x_{i_1}\cdots x_{i_k}$ (planted) or $s=w_\beta$, one independent uniform sign per multiset (null, Remark 1.2). A variant observes only the distinct-index entries. In the (ρ, η) parametrization $\delta=N^{-k\rho/4-\eta/2}$ ($\rho=1$: $k$-TensorPCA$_\eta(N)$).
--
--   A **collection** of problems sharing the secret $x$ (footnote 20) is built from independent components; and a memory image can carry a vector of $\{\pm1\}^n$ in its negative cells.
--
--   **Formalization Note** Encodings: a sample list is $M[0]=n$, $M[1]=$ the number of samples $L$, then for $j<L$ the $k+1$ cells from $2+(k+1)j$ holding the indices of $\alpha_j$ (as $0,\dots,n-1$; $k$-sets and multisets as sorted tuples) and $Y_j$; a tensor is $M[0]=N$ and $M[1+c]=Y_{t(c)}$ with $t(c)$ the $c$-th tuple of $[N]^k$ in lexicographic order. All other cells are $0$. Random choices are read from disjoint streams of the tapes, so they are independent; $\mathrm{Rad}(\delta)$ is $+1$ iff a uniform value is $<(1+\delta)/2$ (so for $\delta\ge1$ it is always $+1$); $\mathrm{Pois}(m)$ is drawn by inversion of its distribution function. For $n<k$ (no index object) the instance is a junk default; only large $n$ matter. Without replacement, the random order sorts the objects by the keys $-\log(u_\alpha)/w(\alpha)$ with $u_\alpha$ i.i.d. Uniform$(0,1)$ and $w(\alpha)$ the object's weight ($1$, or for FULL the number of tuples of $[n]^k$ with that multiset), which is successive sampling without replacement proportional to $w$. A collection interleaves its components' cells (cell $Rq+r$ is cell $q$ of component $r$).
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 22 (PDF 25), Definition 6.1, Fig. 6, footnote 19; p. 81 (PDF 84), Definition A.1; pp. 94–95 (PDF 97–98), Definition 6.1 restated, Definition C.1; pp. 1–3 (PDF 4–6), Eq. (2), Remark 1.2, Definition 1.1; p. 24 (PDF 27), Eq. (19)

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Machine

set_option autoImplicit false

/-!
# The planted k-XOR / k-Gauss model family and k-Tensor PCA

G. Bresler, A. Harbuzova, *Average-Case Reductions for k-XOR and Tensor PCA*, arXiv:2601.19016
(copy sha256 6ec029a7…): Definition 6.1 (p. 22), Fig. 6 (p. 22), Definition C.1 (p. 95),
Definition A.1 (p. 81), Eq. (2) (pp. 1–2), Eq. (19) (p. 24), Remark 1.2 (p. 3), §3 and
Definition 1.1 (the (ρ, η) parametrization), footnote 19 (Rad(δ)).

**Problems as samplers.** A planted problem at signal dimension `n` (`Task n`) is a sampler of the
null instance and, for each secret `x ∈ {±1}ⁿ`, of the planted instance, from one pair of
random tapes (`Tapes`, law `tapeLaw`: i.i.d. Uniform(0,1) and i.i.d. N(0,1) cells). Every
random choice of the model reads its own cells, so distinct choices are independent. The law of
an instance is the push-forward of `tapeLaw`.

**Encodings.** A sample list `{(α_j, Y_j)}_{j<L}` with index tuples `α_j : Fin k → ℕ` is the
memory image `M[0] = n`, `M[1] = L`, and for `j < L` the block of `k + 1` cells from
`2 + (k+1)j` holding `α_j(0), …, α_j(k−1)` (indices `0, …, n−1` as reals) and `Y_j`; all other
cells `0`. A tensor `Y : [N]^k → ℝ` is `M[0] = N` and `M[1 + c] = Y_{t(c)}` where `t(c)` is the
`c`-th tuple of `[N]^k` in lexicographic order, `c < N^k`; all other cells `0`.
-/

namespace KXorTPCA.Reduction

/-- A planted problem at signal dimension `n`: samplers of the null instance and of the
planted instance with secret `x`. -/
structure Task (n : ℕ) where
  /-- The null (pure noise) instance. -/
  null : Tapes → (ℤ → ℝ)
  /-- The planted instance with secret signal `x`. -/
  planted : Signal n → Tapes → (ℤ → ℝ)

/-- A family of problem sequences indexed by a parameter pair (for the k-XOR family the pair
`(ρ, η)`): `F a b n` is the problem at parameters `(a, b)` and dimension `n`. -/
abbrev Family := ℝ → ℝ → (n : ℕ) → Task n

/-- Choice (1) of Fig. 6: the noise model. -/
inductive Noise
  /-- `Y = x_α · Rad(δ)`. -/
  | xor
  /-- `Y = δ x_α + N(0, 1)`. -/
  | gauss

/-- Choice (2) of Fig. 6: the number of samples. -/
inductive Count
  /-- `⌊m⌋` samples. -/
  | fixed
  /-- `Pois(m)` samples. -/
  | pois

/-- Choice (3) of Fig. 6: the index space. -/
inductive IndexSpace
  /-- k-sets of distinct indices (default). -/
  | subsets
  /-- k-multisets with the measure `μ` of Definition A.1 (`FULL`). -/
  | full
  /-- ordered k-tuples of distinct indices (`asymm`). -/
  | asymm

/-- Choice (4) of Fig. 6: sampling of the index sets. -/
inductive Sampling
  /-- with replacement (default). -/
  | wr
  /-- without replacement (`wor`). -/
  | wor

/-- A model of Fig. 6: one option for each of the four choices. -/
structure Choices where
  /-- Choice (1). -/
  noise : Noise
  /-- Choice (2). -/
  count : Count
  /-- Choice (3). -/
  index : IndexSpace
  /-- Choice (4). -/
  sampling : Sampling

/-- The default choices (2)–(4) with noise `nz`: `k-XOR` for `.xor`, `k-Gauss` for `.gauss`. -/
def Choices.std (nz : Noise) : Choices := ⟨nz, .fixed, .subsets, .wr⟩

/-- Cell `i` of stream `s` of a tape (streams are disjoint sub-sequences of the tape). -/
def stream (u : ℕ → ℝ) (s i : ℕ) : ℝ := u (Nat.pair s i)

/-- `Rad(δ)` from a Uniform(0,1) value `u`: `+1` if `u < (1+δ)/2`, else `−1`; so
`P(+1) = (1+δ)/2` and `E[Rad(δ)] = δ` for `δ ∈ [−1, 1]` (footnote 19). -/
noncomputable def rad (δ u : ℝ) : ℝ := if u < (1 + δ) / 2 then 1 else -1

/-- A uniform random sign from a Uniform(0,1) value. -/
noncomputable def unifSign (u : ℝ) : ℝ := if u < 1 / 2 then 1 else -1

/-- `Pois(m)` by inversion of its distribution function at a Uniform(0,1) value `u`. -/
noncomputable def poisInv (m u : ℝ) : ℕ :=
  sInf {j : ℕ | u < ∑ i ∈ Finset.range (j + 1), Real.exp (-m) * m ^ i / (Nat.factorial i)}

/-- All tuples `[n]^k` (indices `0, …, n−1`). -/
def tuples (k n : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Finset.range n

open Classical in
/-- The index objects of each index space, as canonical tuples: strictly increasing tuples for
k-sets, non-decreasing tuples for k-multisets, injective tuples for ordered tuples of distinct
indices. -/
noncomputable def indexObjects (c : IndexSpace) (k n : ℕ) : Finset (Fin k → ℕ) :=
  match c with
  | .subsets => (tuples k n).filter StrictMono
  | .full => (tuples k n).filter Monotone
  | .asymm => (tuples k n).filter Function.Injective

/-- The element with position `⌊u · |s|⌋` of a fixed enumeration of `s`: uniform on `s` when
`u ∼ Uniform(0,1)` (a default element when `s` is empty). -/
noncomputable def pick {α : Type} [Inhabited α] (s : Finset α) (u : ℝ) : α :=
  s.toList.getD ⌊u * s.card⌋₊ default

/-- The non-decreasing rearrangement of a tuple. -/
noncomputable def sortTuple {k : ℕ} (t : Fin k → ℕ) : Fin k → ℕ :=
  fun i => ((List.ofFn t).mergeSort (fun a b => decide (a ≤ b))).getD i 0

/-- An injective code of a tuple with entries `< n`. -/
def tupleCode {k : ℕ} (n : ℕ) (t : Fin k → ℕ) : ℕ := ∑ i, t i * n ^ (i : ℕ)

/-- One index draw with replacement from a Uniform(0,1) value: uniform on k-sets / ordered
k-tuples of distinct indices; for `FULL`, a uniform tuple of `[n]^k` made unordered, which is the
measure `μ({i₁,…,i_k}) ∝ #{(j₁,…,j_k) ∈ [n]^k : {j₁,…,j_k} = {i₁,…,i_k}}` of Definition A.1. -/
noncomputable def drawIndex (c : IndexSpace) (k n : ℕ) (u : ℝ) : Fin k → ℕ :=
  match c with
  | .full => sortTuple (pick (tuples k n) u)
  | _ => pick (indexObjects c k n) u

open Classical in
/-- The weight of an index object under the sampling measure of its index space: `1` for k-sets
and ordered k-tuples (uniform), and for `FULL` the number of tuples `(j₁,…,j_k) ∈ [n]^k` whose
non-decreasing rearrangement is the multiset, i.e. the measure `μ` of Definition A.1 up to
normalisation. -/
noncomputable def objWeight (c : IndexSpace) (k n : ℕ) (a : Fin k → ℕ) : ℝ :=
  match c with
  | .full => (((tuples k n).filter (fun t => sortTuple t = a)).card : ℝ)
  | _ => 1

/-- The index objects in a random order for sampling without replacement from the index space's
measure: object `a` gets the key `−log(u_a) / w(a)` (an Exp(`w(a)`) variable for
`u_a ∼ Uniform(0,1)` i.i.d.) and the objects are sorted by increasing key, so each next object is
drawn from the remaining ones with probability proportional to its weight `w = objWeight`
(uniformly for k-sets and ordered tuples, proportionally to `μ` for `FULL`). -/
noncomputable def randomOrder (c : IndexSpace) (k n : ℕ) (key : (Fin k → ℕ) → ℝ) :
    List (Fin k → ℕ) :=
  (indexObjects c k n).toList.mergeSort (fun a b => decide
    (-Real.log (key a) / objWeight c k n a ≤ -Real.log (key b) / objWeight c k n b))

/-- `x_i` as a real for an index `i : ℕ` (`1` outside `[n]`). -/
def sgnAt {n : ℕ} (x : Signal n) (i : ℕ) : ℝ :=
  if h : i < n then ((x ⟨i, h⟩ : ℤ) : ℝ) else 1

/-- `x_α = ∏_{i ∈ α} x_i`, with multiplicity. -/
def prodAt {n k : ℕ} (x : Signal n) (t : Fin k → ℕ) : ℝ := ∏ i, sgnAt x (t i)

/-- The memory image of a sample list (see the module docstring). -/
noncomputable def encSamples (n k L : ℕ) (idx : ℕ → (Fin k → ℕ)) (val : ℕ → ℝ) : ℤ → ℝ :=
  fun z =>
    if z = 0 then (n : ℝ)
    else if z = 1 then (L : ℝ)
    else if 2 ≤ z then
      let q := (z - 2).toNat / (k + 1)
      let r := (z - 2).toNat % (k + 1)
      if q < L then (if h : r < k then ((idx q ⟨r, h⟩ : ℕ) : ℝ) else val q) else 0
    else 0

/-- The sampler of a model of Fig. 6 with order `k`, dimension `n`, sample parameter `m` and
signal level `δ`; `sig = some x` is the planted instance with secret `x` (Definition 6.1),
`sig = none` the null instance (Definition C.1: `x_α` replaced by an independent uniform sign
`w_j`).
* sample count: `⌊m⌋` (fixed) or `Pois(m)` (Poissonized);
* with replacement: `α_j` i.i.d. from the index space (`drawIndex`); without replacement: the
  first `min(count, #index objects)` index objects in the random order `randomOrder` (successive draws without replacement from the index space's measure: uniform, or `μ` for FULL);
* values: `Y_j = s_j · Rad(δ)` (k-XOR) or `Y_j = δ s_j + G_j`, `G_j ∼ N(0,1)` (k-Gauss), with
  `s_j = x_{α_j}` (planted) or `s_j = w_j` (null). -/
noncomputable def model (ch : Choices) (k n : ℕ) (m δ : ℝ) (sig : Option (Signal n))
    (ω : Tapes) : ℤ → ℝ :=
  let u := ω.1
  let M : ℕ := match ch.count with
    | .fixed => ⌊m⌋₊
    | .pois => poisInv m (stream u 0 0)
  let L : ℕ := match ch.sampling with
    | .wr => M
    | .wor => min M (indexObjects ch.index k n).card
  let idx : ℕ → (Fin k → ℕ) := match ch.sampling with
    | .wr => fun j => drawIndex ch.index k n (stream u 1 j)
    | .wor => fun j =>
        (randomOrder ch.index k n (fun a => stream u 4 (tupleCode n a))).getD j (fun _ => 0)
  let s : ℕ → ℝ := fun j => match sig with
    | some x => prodAt x (idx j)
    | none => unifSign (stream u 3 j)
  let val : ℕ → ℝ := fun j => match ch.noise with
    | .xor => s j * rad δ (stream u 2 j)
    | .gauss => δ * s j + ω.2 j
  encSamples n k L idx val

/-- The planted problem of a model of Fig. 6 at `(k, n, m, δ)`. -/
noncomputable def modelTask (ch : Choices) (k n : ℕ) (m δ : ℝ) : Task n :=
  ⟨model ch k n m δ none, fun x => model ch k n m δ (some x)⟩

/-- The (ρ, η) parametrization (§3, Definition 1.1, Definition 6.1 restated p. 94):
`k-model_{ρ,η}(n)` is the model with `m = n^{k(1+ρ)/2}` and `δ = n^{−kρ/4−η/2}`. -/
noncomputable def kModel (ch : Choices) (k : ℕ) : Family :=
  fun ρ η n => modelTask ch k n ((n : ℝ) ^ ((k : ℝ) * (1 + ρ) / 2))
    ((n : ℝ) ^ (-((k : ℝ) * ρ) / 4 - η / 2))

/-- The `k`-tuple of `[N]^k` with lexicographic position `c` (first coordinate most
significant). -/
def lexTuple (k N c : ℕ) : Fin k → ℕ := fun i => (c / N ^ (k - 1 - (i : ℕ))) % N

/-- The sampler of the order-`k` Tensor PCA instance of Eq. (2)/(19):
`Y_{i₁…i_k} = δ s_{i₁…i_k} + G_{{i₁,…,i_k}}` for every `(i₁,…,i_k) ∈ [N]^k`, with one
independent `G_β ∼ N(0,1)` per k-multiset `β` ("G is a symmetric tensor of N(0,1)"), and
`s = x_{i₁}⋯x_{i_k}` (planted) or `s = w_β`, one independent uniform sign per multiset (null,
Remark 1.2). With `distinctOnly = true` only the distinct-index entries are observed (entries with
a repeated index are `0`). -/
noncomputable def tpca (k N : ℕ) (δ : ℝ) (distinctOnly : Bool) (sig : Option (Signal N))
    (ω : Tapes) : ℤ → ℝ :=
  fun z =>
    if z = 0 then (N : ℝ)
    else if 1 ≤ z ∧ (z - 1).toNat < N ^ k then
      let t := lexTuple k N (z - 1).toNat
      let β := tupleCode N (sortTuple t)
      let s : ℝ := match sig with
        | some x => prodAt x t
        | none => unifSign (stream ω.1 5 β)
      if distinctOnly = true ∧ ¬ Function.Injective t then 0 else δ * s + ω.2 β
    else 0

/-- `k-TensorPCA(N, δ)` as a planted problem. -/
noncomputable def tpcaTask (k N : ℕ) (δ : ℝ) (distinctOnly : Bool) : Task N :=
  ⟨tpca k N δ distinctOnly none, fun x => tpca k N δ distinctOnly (some x)⟩

/-- `k-TensorPCA` in the (ρ, η) parametrization: `δ = N^{−kρ/4−η/2}` (so `ρ = 1` gives
`k-TensorPCA_η(N)`, `δ = N^{−k/4−η/2}`, Eq. (19)). -/
noncomputable def tpcaFam (k : ℕ) (distinctOnly : Bool) : Family :=
  fun ρ η N => tpcaTask k N ((N : ℝ) ^ (-((k : ℝ) * ρ) / 4 - η / 2)) distinctOnly

/-- The tapes of the `r`-th independent component. -/
def subTapes (ω : Tapes) (r : ℕ) : Tapes :=
  (fun i => ω.1 (Nat.pair r i), fun i => ω.2 (Nat.pair r i))

/-- `R` memory images interleaved into one: cell `R q + r` (`0 ≤ r < R`) holds cell `q` of
image `r`. -/
def interleaveMem {R : ℕ} (f : Fin R → (ℤ → ℝ)) : ℤ → ℝ :=
  fun z => if h : (z % (R : ℤ)).toNat < R then f ⟨(z % (R : ℤ)).toNat, h⟩ (z / (R : ℤ)) else 0

/-- A collection of independent instances sharing the same secret `x` (footnote 20). -/
def bundle {n R : ℕ} (T : Fin R → Task n) : Task n :=
  ⟨fun ω => interleaveMem fun r => (T r).null (subTapes ω r),
   fun x ω => interleaveMem fun r => (T r).planted x (subTapes ω r)⟩

/-- A memory image `y` together with a vector `x ∈ {±1}ⁿ` written in cells `−1, …, −n`
(`x_i` in cell `−(i+1)`); used for the input `(Y, x̂′)` of a recovery map and for a
signal-annotated instance. -/
def withSig {n : ℕ} (y : ℤ → ℝ) (x : Signal n) : ℤ → ℝ :=
  fun z => if z < 0 then (if h : (-z - 1).toNat < n then ((x ⟨(-z - 1).toNat, h⟩ : ℤ) : ℝ) else 0)
    else y z

end KXorTPCA.Reduction


