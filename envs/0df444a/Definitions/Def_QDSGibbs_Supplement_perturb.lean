-- Prove2me | Definitions.Def_QDSGibbs_Supplement_perturb
-- name    : QDSGibbs_Supplement_perturb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:25:05.674934+00:00
-- url     : https://prove2.me/theorems/e181c4e0-d7ed-47df-8b5c-31bab7a83257
-- title:
--   Perturbed interaction $H=H^{(0)}+Q$, perturbation strength $\delta$, metric geometry and polynomial volume growth
-- statement:
--   Let $\Lambda$ be a finite set of $N$ sites with local dimensions $d_i$, and let interactions be written as in (2.1), $H=\sum_i V_i+\sum_\alpha h_\alpha$ with labelled supports $X_\alpha$.
--
--   1. **Perturbed interaction.** For a reference interaction $H^{(0)}$ and a perturbation $Q$ (itself an interaction: single-site terms $Q_{\{i\}}$ and labelled multi-site terms $Q_X$), $H=H^{(0)}+Q$ is the labelled interaction whose terms are those of $H^{(0)}$ followed by those of $Q$, with on-site terms $V^{(0)}_i+Q_{\{i\}}$.
--   2. **Crossing.** A support $X$ crosses a block $B$ if $X\cap B\neq\emptyset$ and $X\cap B^c\neq\emptyset$.
--   3. **Perturbation strength.** $$\delta=\sup_{i\in\Lambda}\sum_{X\ni i}\|Q_X\|,$$ the sum including the single-site perturbation at $i$; $\|\cdot\|$ is the operator norm.
--   4. **Geometry.** A metric $\mathrm{dist}$ on $\Lambda$, the neighbourhoods $U^{\le u}=\{i:\mathrm{dist}(i,U)\le u\}$, **polynomial volume growth** $|U^{\le u}|\le C_{\mathrm{vol}}|U|(1+u)^D$ for nonempty $U$ and $u\ge0$, and the bookkeeping bounds of (2.1): $2\le|X_\alpha|\le k$, $\operatorname{diam}X_\alpha\le r$, each site in at most $\nu$ supports counting labels.
--
--   These are the data of the stability theorem (Theorem 6.1).
--
--   **Formalization Note** The perturbed interaction is `perturb I0 Q` with `Fin.append` of the labelled families, so `ham (perturb I0 Q) = ham I0 + ham Q`. The exponent $D$ is real.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (2.1) p.10; polynomial volume growth p.11; (6.1) p.53; (6.2) p.54

import Mathlib
import Definitions.Def_QDSGibbs_Interaction

open scoped Matrix

namespace QDSGibbs.Supplement

/-- The **perturbed interaction** `H = H^{(0)} + Q` as one labelled interaction (Rouzé–Stilck França,
arXiv:2610.03578, held file sha256 ede55815…, (6.1), p.53): the labelled terms of the reference
`H^{(0)}` followed by those of the perturbation `Q`, and on-site terms `V^{(0)}_i + Q_i`.

**Formalization Note** The perturbation is itself an `Interaction`: its single-site terms are its
on-site terms `Q.V i`, its multi-site terms `Q.h α` have supports `Q.X α`. Then
`ham (perturb I0 Q) = ham I0 + ham Q`. -/
def perturb {N : ℕ} {d : Fin N → ℕ} (I0 Q : Interaction d) : Interaction d where
  m := I0.m + Q.m
  X := Fin.append I0.X Q.X
  h := Fin.append I0.h Q.h
  V := fun i => I0.V i + Q.V i

/-- The support `X` **crosses** `B`: it meets both `B` and `B^c` (arXiv:2610.03578, (2.4), p.11). -/
def Crosses {N : ℕ} (X B : Finset (Fin N)) : Prop :=
  (X ∩ B).Nonempty ∧ (X \ B).Nonempty

open Classical in
/-- The **perturbation strength** `δ = sup_i Σ_{X ∋ i} ‖Q_X‖` (arXiv:2610.03578, (6.1), p.53),
including the single-site perturbations `Q_{{i}} = Q.V i`.

**Formalization Note** A real supremum over the finitely many sites; `‖·‖` is the operator norm. -/
noncomputable def pertNorm {N : ℕ} {d : Fin N → ℕ} (Q : Interaction d) : ℝ :=
  ⨆ i : Fin N, (opNorm (Q.V i) + ∑ α ∈ Finset.univ.filter (fun α => i ∈ Q.X α), opNorm (Q.h α))

/-- `dist` is a **metric** on the sites (arXiv:2610.03578, §2.1, p.10: the underlying graph distance,
or the ℓ∞ distance on a lattice). -/
def IsMetric {N : ℕ} (dist : Fin N → Fin N → ℝ) : Prop :=
  (∀ i j, dist i j = 0 ↔ i = j) ∧ (∀ i j, dist i j = dist j i) ∧
    ∀ i j k, dist i k ≤ dist i j + dist j k

open Classical in
/-- The neighbourhood `U^{≤u} = {i ∈ Λ : dist(i, U) ≤ u}` (arXiv:2610.03578, §2.1, p.10). -/
noncomputable def nbhdM {N : ℕ} (dist : Fin N → Fin N → ℝ) (U : Finset (Fin N)) (u : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter fun i => ∃ j ∈ U, dist i j ≤ u

/-- **Polynomial volume growth** with constants `C_vol`, `D` (arXiv:2610.03578, §2.1, p.11):
`|U^{≤u}| ≤ C_vol |U| (1 + u)^D` for every nonempty `U ⊆ Λ` and `u ≥ 0`.

**Formalization Note** `D` is a real exponent (`Real.rpow`); integer exponents are the special case. -/
def PolyGrowth {N : ℕ} (dist : Fin N → Fin N → ℝ) (Cvol D : ℝ) : Prop :=
  ∀ U : Finset (Fin N), U.Nonempty → ∀ u : ℝ, 0 ≤ u →
    ((nbhdM dist U u).card : ℝ) ≤ Cvol * (U.card : ℝ) * (1 + u) ^ D

open Classical in
/-- The bookkeeping bounds of (2.1) (arXiv:2610.03578, p.10): every labelled support has
`2 ≤ |X_α| ≤ k` and `diam X_α ≤ r`, and each site belongs to at most `ν` supports, counting labels. -/
def IsBoundedGeometry {N : ℕ} {d : Fin N → ℕ} (dist : Fin N → Fin N → ℝ) (I : Interaction d)
    (k : ℕ) (r : ℝ) (ν : ℕ) : Prop :=
  (∀ α, 2 ≤ (I.X α).card ∧ (I.X α).card ≤ k ∧ ∀ i ∈ I.X α, ∀ j ∈ I.X α, dist i j ≤ r) ∧
    ∀ i : Fin N, (Finset.univ.filter fun α => i ∈ I.X α).card ≤ ν

end QDSGibbs.Supplement


