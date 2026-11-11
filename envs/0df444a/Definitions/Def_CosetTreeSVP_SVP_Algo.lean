-- Prove2me | Definitions.Def_CosetTreeSVP_SVP_Algo
-- name    : CosetTreeSVP_SVP_Algo
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:33:45.474521+00:00
-- url     : https://prove2.me/theorems/c2a35978-2758-47d1-82ee-3b917ecc63fc
-- title:
--   Machine encodings: the discrete Gaussian sampler's input and output law, bounded distance decoding and a successful advice, and the input/output words of Algorithm 1
-- statement:
--   The algorithmic statements run on the published randomized log-cost rational RAM `TwMSOCount.Main` (fair coin tape, bit time, bit space). A rational basis $B \in \mathbb Q^{n\times n}$ gives the real lattice $L(B)$ (`latQ`), with lattice points $Bx$, $x \in \mathbb Z^n$ (`latPt`). Words are lists of rationals; the bit length of a word is the sum of the bit lengths of its entries (`wordBits`).
--
--   **Sampling (Theorem 2.2).** The input word is the basis, then $\sigma \in \mathbb Q_{>0}$, $\kappa$ and $M$; an output of $M$ lattice vectors $Bx_1,\dots,Bx_M$ is the word of their integer coefficient vectors. The law of $M$ independent samples of $D_{L,\sigma}$ on these words is `iidLaw`, the output law of a program under fair coins is `outLaw`, and their statistical distance is $\tfrac12\sum_o|\mu(o)-\nu(o)|$ (`tvDist`).
--
--   **Bounded distance decoding (Definition 2.5, Theorem 2.6).** A target $y \in \mathbb Q^n$ is an $\alpha$-BDD instance if $\operatorname{dist}(y, L) < \alpha\lambda_1(L)$; $x$ is the coefficient vector of a closest lattice vector if $\|y - Bx\| \le \|y - Bz\|$ for all $z \in \mathbb Z^n$. An advice word $a$ is **successful** for a query program $P_q$ (with an $o(n)$ function $g$ and exponent $K$) if for every $n^{-1/3}$-BDD instance $y$, the run of $P_q$ on the word $a$ followed by $y$ halts on every coin tape with the coefficient vector of the closest lattice vector, within bit time $2^{g(n)}(\ell+\ell_y+1)^K$ and bit space at most the advice's own stored bits plus $(\ell+\ell_y+1)^K$, where $\ell$, $\ell_y$ are the bit lengths of $B$ and $y$. `preSuccess` is the event that the preprocessing program outputs a successful advice.
--
--   **Algorithm 1 (Lemma 4.8).** The input word holds $B$, the matrix $U$ (entries in $\{0,\dots,q-1\}$), the samples $X_{r,i} = B^{-T}z_{r,i}$ as integer coordinate vectors $z_{r,i}$, and $\delta$ (each $\delta_{j,a}$ as $n$ entries). A correct output lists every $\theta \in H_m$ exactly once, each with rational vectors $c_{\theta,0},\dots,c_{\theta,q-1}$ such that
--   $$\hat A_\delta(\theta) = 2\pi i\sum_{k=0}^{q-1}\omega_q^k\,c_{\theta,k}$$
--   (an exact encoding: $\hat A_\delta(\theta)/(2\pi i) \in \mathbb Q(\omega_q)^n$ for rational $B$). `sampleBits` is the largest bit length of one sample's coordinate vector.
--
--   **Formalization Note.** `realB`, `latQ`, `latPt`, `qVec`, `encQVec`, `wordBits`, `encDGS`, `encSamples`, `iidLaw`, `outLaw`, `tvDist`, `IsClosest`, `IsBDDInstance`, `AdviceGood`, `preSuccess`, `famAt`, `encAlg1`, `dualPt`, `sampleBits`, `encAhatOut`, `AhatOutputOK`. Every encoding is computable and fixed in advance (row-major for matrices, $r$ outer and $i$ inner for samples, $j$ outer and $a$ inner for $\delta$).
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), pp. 11–12 (PDF 13–14), Theorem 2.2, Definition 2.5, Theorem 2.6; p. 20 (PDF 22), Lemma 4.8 and Algorithm 1

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace CosetTreeSVP.SVP

/-! ### Rational inputs -/

/-- A rational basis viewed as a real matrix. -/
noncomputable def realB {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  B.map (fun x => (x : ℝ))

/-- The lattice `L(B) = BZⁿ ⊂ ℝⁿ` of a rational basis. -/
noncomputable def latQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Submodule ℤ (E n) :=
  SuperlatSVP.lat (realB B)

/-- The real point `Bx` of an integer coefficient vector `x`. -/
noncomputable def latPt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) : E n :=
  WithLp.toLp 2 ((realB B).mulVec (fun k => (x k : ℝ)))

/-- A rational vector viewed in `ℝⁿ`. -/
noncomputable def qVec {n : ℕ} (y : Fin n → ℚ) : E n := WithLp.toLp 2 (fun k => (y k : ℝ))

/-- The word of a rational vector: its `n` entries. -/
def encQVec {n : ℕ} (y : Fin n → ℚ) : List ℚ := (List.finRange n).map y

/-- Total bit length of a word. -/
def wordBits (w : List ℚ) : ℕ := (w.map qbits).sum

/-! ### Discrete Gaussian sampling (Theorem 2.2) -/

/-- Input word of the sampler: the basis (`SuperlatSVP.encBasis`), then `σ`, `κ`, `M`. -/
def encDGS {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (σ : ℚ) (κ M : ℕ) : List ℚ :=
  SuperlatSVP.encBasis B ++ [σ, (κ : ℚ), (M : ℚ)]

/-- Output word of `M` lattice vectors `Bx₁, …, Bx_M`: their integer coefficient vectors, one after
the other. -/
def encSamples {n M : ℕ} (x : Fin M → Fin n → ℤ) : List ℚ :=
  (List.finRange M).flatMap fun i => SuperlatSVP.encIntVec (x i)

/-- Probability that `M` independent samples of `D_{L(B),σ}` have the output word `o`. -/
noncomputable def iidLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (σ : ℝ) (M : ℕ) (o : List ℚ) :
    ℝ≥0∞ := by
  classical
  exact ∑' x : Fin M → Fin n → ℤ, if encSamples x = o then
    ∏ i, ENNReal.ofReal (RegevLWE.GaussConv.rho σ (latPt B (x i)) /
      RegevLWE.Hyperplane.rhoLattice σ (latQ B)) else 0

/-- Probability, under fair coins, that the run of `P` from `c` halts with output word `o`. -/
noncomputable def outLaw (P : Program) (c : Config) (o : List ℚ) : ℝ≥0∞ :=
  coinTape {τ | callOutput P c τ = some o}

/-- Statistical distance `½ Σ_o |μ(o) − ν(o)|` of two laws on output words. -/
noncomputable def tvDist (μ ν : List ℚ → ℝ≥0∞) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑' o : List ℚ, ((μ o - ν o) + (ν o - μ o))

/-! ### Bounded distance decoding (Definition 2.5, Theorem 2.6) -/

/-- `x` is the coefficient vector of a closest lattice vector to `y`: `‖y − Bx‖ = dist(y, L)`. -/
def IsClosest {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) (x : Fin n → ℤ) : Prop :=
  ∀ z : Fin n → ℤ, ‖qVec y - latPt B x‖ ≤ ‖qVec y - latPt B z‖

/-- An `α`-BDD instance on `L(B)`: a target `y` with `dist(y, L) < α λ₁(L)` (Definition 2.5). -/
def IsBDDInstance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (α : ℝ) (y : Fin n → ℚ) : Prop :=
  Metric.infDist (qVec y) (latQ B : Set (E n)) < α * SuperlatSVP.lam1 (latQ B)

/-- The advice `a` (an output word of the preprocessing) is successful for `L(B)`: from the input
word `a ++ y` the query program `Pq` solves every `n^{−1/3}`-BDD instance `y` deterministically —
on every coin tape it halts with the coefficient vector of the closest lattice vector, within bit
time `2^{g(n)}·(ℓ + ℓ_y + 1)^K` and within bit space `|a| + (ℓ + ℓ_y + 1)^K` (the advice's own
stored bits plus polynomial additional space), `ℓ` the bit length of `B`, `ℓ_y` that of `y`. -/
def AdviceGood (Pq : Program) (g : ℕ → ℝ) (K : ℕ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (a : List ℚ) : Prop :=
  ∀ y : Fin n → ℚ, IsBDDInstance B ((n : ℝ) ^ (-(1 / 3 : ℝ))) y →
    ∀ τ : ℕ → Bool, ∃ s : RunStats, runStats Pq τ (Config.init (a ++ encQVec y)) = some s ∧
      (∃ x : Fin n → ℤ, IsClosest B y x ∧ s.final.output = SuperlatSVP.encIntVec x) ∧
      (s.time : ℝ) ≤ (2 : ℝ) ^ g n *
        ((SuperlatSVP.inputBits B : ℝ) + wordBits (encQVec y) + 1) ^ K ∧
      (s.space : ℝ) ≤ (Config.init a).spaceBits +
        ((SuperlatSVP.inputBits B : ℝ) + wordBits (encQVec y) + 1) ^ K

/-- The event that the preprocessing `Ppre` on `B` halts with a successful advice. -/
def preSuccess (Ppre Pq : Program) (g : ℕ → ℝ) (K : ℕ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    Set (ℕ → Bool) :=
  {τ | ∃ a : List ℚ, callOutput Ppre (Config.init (SuperlatSVP.encBasis B)) τ = some a ∧
    AdviceGood Pq g K B a}

/-! ### Algorithm 1 (Lemma 4.8) -/

/-- The family `δ` read at `(j, a)` (level `j ∈ [m−1]`, `a ∈ [0, p/2^j)`), `0` elsewhere. -/
def famAt {n p m q : ℕ} (δ : Fam n p m q) (j a : ℕ) : Fin n → ZMod q :=
  if h : 1 ≤ j ∧ j - 1 < m - 1 then
    if h' : a < p / 2 ^ (j - 1 + 1) then (δ ⟨⟨j - 1, h.2⟩, ⟨a, h'⟩⟩).val else 0
  else 0

/-- Input word of Algorithm 1: the basis `B`, the matrix `U` (entries in `{0, …, q−1}`, row by
row), the samples `X_{r,i} = B^{−T} z_{r,i}` as integer coordinate vectors `z_{r,i}` (`r` outer,
`i` inner), and the shifts `δ_{j,a}` (`j` outer, `a` inner, each as `n` entries in
`{0, …, q−1}`). -/
def encAlg1 {n p m q N : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (z : Fin p → Fin N → Fin n → ℤ)
    (δ : Fam n p m q) : List ℚ :=
  SuperlatSVP.encBasis B ++
    ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
      (((U : Matrix (Fin n) (Fin n) (ZMod q)) i j).val : ℚ)) ++
    ((List.finRange p).flatMap fun r => (List.finRange N).flatMap fun i =>
      SuperlatSVP.encIntVec (z r i)) ++
    ((List.range (m - 1)).flatMap fun j => (List.range (p / 2 ^ (j + 1))).flatMap fun a =>
      (List.finRange n).map fun k => ((famAt δ (j + 1) a k).val : ℚ))

/-- The dual vector `B^{−T} z ∈ L*` of an integer coordinate vector `z`. -/
noncomputable def dualPt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℤ) : E n :=
  WithLp.toLp 2 (fun k => ((B⁻¹.transpose.mulVec (fun i => (z i : ℚ))) k : ℝ))

/-- Largest bit length of one sample's coordinate vector. -/
def sampleBits {n p N : ℕ} (z : Fin p → Fin N → Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun ri : Fin p × Fin N => wordBits (SuperlatSVP.encIntVec (z ri.1 ri.2))

/-- Output word of Algorithm 1: for each listed `θ`, its `n` entries in `{0, …, q−1}`, then the
`q` rational vectors `c_{θ,0}, …, c_{θ,q−1}`. -/
def encAhatOut {n q : ℕ} (l : List ((Fin n → ZMod q) × (Fin q → Fin n → ℚ))) : List ℚ :=
  l.flatMap fun e => ((List.finRange n).map fun k => ((e.1 k).val : ℚ)) ++
    ((List.finRange q).flatMap fun k => encQVec (e.2 k))

/-- The output word `o` lists every `θ ∈ H_m` exactly once, each with rational vectors
`c_{θ,0}, …, c_{θ,q−1}` such that `Â_δ(θ) = 2πi Σ_{k<q} ω_q^k c_{θ,k}` (exact output: `Â_δ(θ)/(2πi)`
lies in `Q(ω_q)ⁿ`). -/
def AhatOutputOK {n p m q N : ℕ} (Q : ℕ) (B : Matrix (Fin n) (Fin n) ℚ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (z : Fin p → Fin N → Fin n → ℤ)
    (δ : Fam n p m q) (o : List ℚ) : Prop :=
  ∃ l : List ((Fin n → ZMod q) × (Fin q → Fin n → ℚ)),
    o = encAhatOut l ∧ (l.map Prod.fst).Nodup ∧
    (∀ θ : Fin n → ZMod q, θ ∈ l.map Prod.fst ↔ InH m m θ) ∧
    ∀ e ∈ l, Ahat Q (realB B) U δ (fun r i => dualPt B (z r i)) e.1 =
      (2 * Real.pi * Complex.I) •
        ∑ k : Fin q, omegaPow q (k.val : ZMod q) • toC (qVec (e.2 k))

end CosetTreeSVP.SVP


