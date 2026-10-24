-- Prove2me | Definitions.Def_WernerExt_TwoSided_Model
-- name    : WernerExt_TwoSided_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:45.399726+00:00
-- url     : https://prove2.me/theorems/cc78bf5e-6fd3-4139-91bc-e6d708d13aff
-- title:
--   Eqs. (1), (2), (4), (7), (9), (11), (12), SM Eqs. (3), (5), pp. 1–3 — Werner states, two-sided extendibility, H_W, Casimirs, d-row partitions, c(λ), λ̂^(AB), E_W
-- statement:
--   The shared objects of the mission. Throughout, $d\ge 2$ is the local dimension, Alice holds $n_A$ and Bob $n_B$ copies of $\mathbb C^d$, and the joint space $(\mathbb C^d)^{\otimes n_A}\otimes(\mathbb C^d)^{\otimes n_B}$ has the computational basis $|x,y\rangle$ with $x:\{1,\dots,n_A\}\to\{1,\dots,d\}$, $y:\{1,\dots,n_B\}\to\{1,\dots,d\}$.
--
--   1. **Flip and Werner states** (Eq. (2), p. 2). $F|a\rangle|b\rangle=|b\rangle|a\rangle$ on $\mathbb C^d\otimes\mathbb C^d$, and for $\alpha\in\mathbb R$
--   $$\rho^W(\alpha)=\frac{d}{d^2-1}\left[(d-\alpha)\frac{\mathbb 1}{d^2}+\left(\alpha-\frac1d\right)\frac{F}{d}\right],$$
--   so that $\operatorname{Tr}\rho^W(\alpha)=1$ and $\operatorname{Tr}(\rho^W(\alpha)F)=\alpha$; it is a state exactly for $\alpha\in[-1,1]$.
--   2. **Extendibility** (Eq. (1), p. 1). For an operator $\hat\rho$ on the joint space, $\operatorname{Tr}_{\overline{A_iB_j}}\hat\rho$ is its partial trace onto Alice's $i$-th and Bob's $j$-th site. $\hat\rho$ is an $(n_A,n_B)$-extension of a two-site state $\rho$ if $\hat\rho\ge 0$, $\operatorname{Tr}\hat\rho=1$ and $\operatorname{Tr}_{\overline{A_iB_j}}\hat\rho=\rho$ for **all** $i,j$; $\rho$ is $(n_A,n_B)$-extendible if it has one.
--   3. **The Hamiltonian** (Eq. (4), p. 2). $H^W=\frac{1}{n_An_B}\sum_{i,j}F_{ij}$, where $F_{ij}$ exchanges Alice's site $i$ with Bob's site $j$. A real $e$ is an eigenvalue of a matrix $H$ if $Hv=ev$ for some $v\neq0$.
--   4. **Generators and Casimirs** (SM Eqs. (3), (5), SM p. 1). $S^{\alpha\beta}=|\beta\rangle\langle\alpha|-\frac1d\delta_{\beta\alpha}\mathbb 1$; on $n$ sites $C_n=\sum_{\alpha,\beta}\big(\sum_iS^{\alpha\beta}_i\big)\big(\sum_jS^{\beta\alpha}_j\big)$, where $S_i$ acts on site $i$. $C_A$, $C_B$, $C_{AB}$ are $C_n$ on Alice's sites, Bob's sites and all $n_A+n_B$ sites (Alice's first).
--   5. **Partitions and dominance** (p. 2, Eq. (7), p. 3). $\lambda\vdash_d n$: $\lambda_1\ge\dots\ge\lambda_d\ge0$ integers with $\sum\lambda_i=n$ (zero rows allowed). $\lambda\trianglerighteq\mu$ iff $\lambda_1+\dots+\lambda_k\ge\mu_1+\dots+\mu_k$ for all $k$; $\lambda$ covers $\mu$ if $\lambda\triangleright\mu$ with no $d$-partition strictly between.
--   6. **Casimir value** (Eq. (9), p. 3). With $n=\sum_i\lambda_i$,
--   $$c(\lambda)=\sum_{i=1}^d\left[\left(\lambda_i-\frac nd\right)^2+2(d-i)\left(\lambda_i-\frac nd\right)\right].$$
--   7. **Minimum product diagram and energy** (Eqs. (11), (12), p. 3). $\hat\lambda^{(AB)}(\lambda^{(A)},\lambda^{(B)})=\operatorname{sort}\{\lambda^{(A)}_i+\lambda^{(B)}_{d-i+1}\}_{i=1}^d$ (decreasing), and
--   $$E^W(\lambda^{(A)},\lambda^{(B)})=\frac{1}{2n_An_B}\left[c(\hat\lambda^{(AB)})-c(\lambda^{(A)})-c(\lambda^{(B)})\right]+\frac1d.$$
--   8. **Duals** (p. 2). The $M$-dual of $\lambda$ is $\bar\lambda_i=M-\lambda_{d-i+1}$, used for $M\ge\lambda_1$.
--   9. **Symmetry groups** (p. 2). $U^{\otimes(n_A+n_B)}$ for $d\times d$ matrices $U$, and the permutation operators of $S_{n_A}\times S_{n_B}$ permuting Alice's and Bob's sites separately.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Sites and rows are 0-based (`Fin n`, `Fin d`); the joint carrier is `Cfg d nA nB = (Fin nA → Fin d) × (Fin nB → Fin d)`. `pairMarginal X i j` sums each traced configuration exactly once. `C_AB` is transported from `Fin (nA+nB) → Fin d` along `Fin.appendEquiv`. In `casimirValue` the 1-based weight $2(d-i)$ becomes `2 * (d - 1 - i)`. `sortDesc` sorts decreasingly via `Tuple.sort`. `EW d nA nB` takes the sizes $n_A,n_B$ as explicit parameters; it is applied to $d$-partitions of $n_A$, $n_B$. `mDual` uses natural-number subtraction and is only applied with $M$ at least every row.
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 1, Eq. (1); p. 2, Eqs. (2), (4) and the labelling paragraph; p. 3, Eqs. (7), (9), (11), (12); Supplemental Material p. 1 (PDF 7), SM Eqs. (3), (5)

import Mathlib

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- The joint configuration space of `nA` Alice sites and `nB` Bob sites, each a `d`-level
system with computational basis `Fin d`. A matrix indexed by `Cfg d nA nB` is an operator on
`(ℂ^d)^{⊗ nA} ⊗ (ℂ^d)^{⊗ nB}`. Sites are 0-based: the paper's `A_i` is `i - 1 : Fin nA`. -/
abbrev Cfg (d nA nB : ℕ) := (Fin nA → Fin d) × (Fin nB → Fin d)

/-- The flip operator `F` on `ℂ^d ⊗ ℂ^d`, `F |x⟩|y⟩ = |y⟩|x⟩` (p. 2). -/
def flip (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- The Werner state of Eq. (2), p. 2:
`ρ_W(α) = d/(d² − 1) [ (d − α) 𝟙/d² + (α − 1/d) F/d ]`, with `α = Tr(ρ_W(α) F)`. -/
def wernerState (d : ℕ) (α : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (((d : ℝ) / ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) •
    ((((((d : ℝ) - α) / (d : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
      ((((α - 1 / (d : ℝ)) / (d : ℝ) : ℝ)) : ℂ) • flip d)

/-- The two-site marginal `Tr_{\overline{A_i B_j}}(X)` of an operator `X` on the joint system:
the partial trace over every site except Alice's site `i` and Bob's site `j` (Eq. (1), p. 1).
Its entry at `((a, b), (a', b'))` is `∑ X((x, y), (x[i ↦ a'], y[j ↦ b']))` over the
configurations `(x, y)` with `x i = a` and `y j = b`; each traced configuration occurs once. -/
def pairMarginal {d nA nB : ℕ} (X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ) (i : Fin nA)
    (j : Fin nB) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun ab ab' =>
    ∑ x : Fin nA → Fin d, ∑ y : Fin nB → Fin d,
      if x i = ab.1 ∧ y j = ab.2 then
        X (x, y) (Function.update x i ab'.1, Function.update y j ab'.2)
      else 0

/-- `X` is an `(nA, nB)`-extension of `ρ`: a state (positive semidefinite, trace one) on
`(ℂ^d)^{⊗ nA} ⊗ (ℂ^d)^{⊗ nB}` whose marginal on `A_i B_j` is `ρ` for **every** `i` and `j`
(Eq. (1), p. 1). -/
def IsExtensionOf {d nA nB : ℕ} (X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, pairMarginal X i j = ρ

/-- A state `ρ` on `ℂ^d ⊗ ℂ^d` is `(nA, nB)`-extendible (Eq. (1), p. 1). -/
def IsExtendible (d nA nB : ℕ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ, IsExtensionOf X ρ

/-- The configuration obtained by exchanging the contents of Alice's site `i` and Bob's
site `j`. -/
def swapCfg {d nA nB : ℕ} (i : Fin nA) (j : Fin nB) (p : Cfg d nA nB) : Cfg d nA nB :=
  (Function.update p.1 i (p.2 j), Function.update p.2 j (p.1 i))

/-- The flip `F_ij` exchanging Alice's site `i` and Bob's site `j` (identity elsewhere):
the permutation matrix of `swapCfg i j`. -/
def flipAB {d nA nB : ℕ} (i : Fin nA) (j : Fin nB) : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  Matrix.of fun p q => if p = swapCfg i j q then 1 else 0

/-- The Hamiltonian of Eq. (4), p. 2: `H_W = (1/(nA nB)) ∑_{i ∈ L, j ∈ R} F_ij`, the sum over
all Alice sites `i` and all Bob sites `j`. -/
def hamW (d nA nB : ℕ) : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  (((nA * nB : ℕ) : ℂ)⁻¹) • ∑ i : Fin nA, ∑ j : Fin nB, flipAB (d := d) i j

/-- `e` is an eigenvalue of `H`: some nonzero vector `v` has `H v = e v`. -/
def IsEigenvalue {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (e : ℝ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ H.mulVec v = (e : ℂ) • v

/-- The `su(d)` generators of SM Eq. (3), SM p. 1:
`S^{αβ} = |β⟩⟨α| − (1/d) δ_{βα} 𝟙` (basis 0-based). -/
def gen (d : ℕ) (a b : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single b a 1 - (if a = b then ((d : ℂ)⁻¹) else 0) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The operator acting as `M` on site `i` of `(ℂ^d)^{⊗ n}` and as the identity on every
other site. -/
def siteOp {d n : ℕ} (i : Fin n) (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => M (x i) (y i) * (if ∀ k, k ≠ i → x k = y k then 1 else 0)

/-- The quadratic Casimir operator of `SU(d)` in the `n`-fold tensor product of the defining
representation, SM Eq. (5), SM p. 1:
`C_n = ∑_{α,β} (∑_i S^{αβ}_i)(∑_j S^{βα}_j)`. -/
def casimirOn (d n : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ a : Fin d, ∑ b : Fin d,
    (∑ i : Fin n, siteOp i (gen d a b)) * (∑ j : Fin n, siteOp j (gen d b a))

/-- `C_A`: the Casimir on Alice's `nA` sites, identity on Bob's. -/
def casimirA (d nA nB : ℕ) : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  casimirOn d nA ⊗ₖ (1 : Matrix (Fin nB → Fin d) (Fin nB → Fin d) ℂ)

/-- `C_B`: the Casimir on Bob's `nB` sites, identity on Alice's. -/
def casimirB (d nA nB : ℕ) : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  (1 : Matrix (Fin nA → Fin d) (Fin nA → Fin d) ℂ) ⊗ₖ casimirOn d nB

/-- `C_AB`: the Casimir on all `nA + nB` sites, transported to `Cfg` along
`Fin.appendEquiv` (Alice's sites first, then Bob's). -/
def casimirAB (d nA nB : ℕ) : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  Matrix.reindex (Fin.appendEquiv nA nB).symm (Fin.appendEquiv nA nB).symm
    (casimirOn d (nA + nB))

/-- The `d`-partitions of `n` (`λ ⊢_d n`, p. 2): weakly decreasing row lengths
`λ_1 ≥ ⋯ ≥ λ_d ≥ 0` (rows of length zero allowed) summing to `n`. Rows are 0-based. -/
def DPart (d n : ℕ) := {l : Fin d → ℕ // Antitone l ∧ ∑ i, l i = n}

/-- Dominance order, Eq. (7), p. 3: `Dominates l m` is `l ⊵ m`, i.e.
`l_1 + ⋯ + l_k ≥ m_1 + ⋯ + m_k` for every `k`. -/
def Dominates {d : ℕ} (l m : Fin d → ℕ) : Prop :=
  ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), m i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), l i

/-- `l` covers `m` in dominance order among the `d`-partitions of `n` (p. 3): `l ▷ m` and no
`d`-partition `ν` of `n` satisfies `l ▷ ν ▷ m`. -/
def Covers {d n : ℕ} (l m : DPart d n) : Prop :=
  Dominates l.1 m.1 ∧ l ≠ m ∧
    ∀ ν : DPart d n, Dominates l.1 ν.1 → Dominates ν.1 m.1 → ν = l ∨ ν = m

/-- The Casimir eigenvalue of Eq. (9), p. 3:
`c(λ) = ∑_{i=1}^d [(λ_i − n/d)² + 2(d − i)(λ_i − n/d)]` with `n = ∑ λ_i`.
With 0-based rows the weight `2(d − i)` becomes `2(d − 1 − i)`. -/
def casimirValue {d : ℕ} (l : Fin d → ℕ) : ℝ :=
  ∑ i : Fin d,
    (((l i : ℝ) - (∑ k, (l k : ℝ)) / d) ^ 2 +
      2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l i : ℝ) - (∑ k, (l k : ℝ)) / d))

/-- The entries of `v` sorted in decreasing order (`sort{…}` of Eqs. (11), (12)). -/
def sortDesc {d : ℕ} (v : Fin d → ℕ) : Fin d → ℕ :=
  fun i => v (Tuple.sort v (Fin.rev i))

/-- The minimum product diagram of Eq. (11), p. 3:
`λ̂^(AB)(λ^A, λ^B) = sort{λ^A_i + λ^B_{d−i+1}}_{i=1}^d`: the rows of `λ^B` reversed, added to
those of `λ^A`, then sorted decreasingly. -/
def minProduct {d : ℕ} (lA lB : Fin d → ℕ) : Fin d → ℕ :=
  sortDesc (fun i => lA i + lB (Fin.rev i))

/-- The energy of Eq. (12), first expression, p. 3:
`E_W(λ^A, λ^B) = [c(λ̂^(AB)(λ^A, λ^B)) − c(λ^A) − c(λ^B)]/(2 nA nB) + 1/d`. -/
def EW (d nA nB : ℕ) (lA lB : Fin d → ℕ) : ℝ :=
  (casimirValue (minProduct lA lB) - casimirValue lA - casimirValue lB) /
      (2 * (nA : ℝ) * (nB : ℝ)) + 1 / (d : ℝ)

/-- The `M`-dual of a row vector, p. 2: `λ̄_i = M − λ_{d−i+1}` (used with `M ≥ λ_1`). -/
def mDual {d : ℕ} (M : ℕ) (l : Fin d → ℕ) : Fin d → ℕ :=
  fun i => M - l (Fin.rev i)

/-- `U^{⊗ n}` on `(ℂ^d)^{⊗ n}`. -/
def tensorPow {d : ℕ} (n : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => ∏ k, U (x k) (y k)

/-- The local unitary `U^{⊗ (nA + nB)}` on the joint system. -/
def localU {d : ℕ} (nA nB : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  tensorPow nA U ⊗ₖ tensorPow nB U

/-- The bipartite permutation `(σ, τ) ∈ S_{nA} × S_{nB}` acting on the joint system by
permuting Alice's sites by `σ` and Bob's by `τ`: the permutation matrix sending the basis
vector `|x, y⟩` to `|x ∘ σ⁻¹, y ∘ τ⁻¹⟩`. -/
def permCfg {d nA nB : ℕ} (σ : Equiv.Perm (Fin nA)) (τ : Equiv.Perm (Fin nB)) :
    Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∘ σ.symm ∧ p.2 = q.2 ∘ τ.symm then 1 else 0

end

end WernerExt.TwoSided


