-- Prove2me | Definitions.Def_PolyEulerFlow_IsForcedSolution
-- name    : PolyEulerFlow_IsForcedSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:21.049358+00:00
-- url     : https://prove2.me/theorems/f1898652-74cb-4844-baff-dbe219792541
-- title:
--   Forced solutions, permitted forcings, cell averages and continuous phase entries
-- statement:
--   The continuous semantics (Theorem 1, Corollary 50, Lemma 16).
--
--   A **forced solution** of $\dot z=f(z)+\xi(t)$, $z(0)=z_0$, is a function $z$ continuous on $[0,\infty)$ such that for every $t\ge0$ the integrand $u\mapsto f(z(u))+\xi(u)$ is integrable on $[0,t]$ and
--   $$z(t)=z_0+\int_0^t\big(f(z(u))+\xi(u)\big)\,du .$$
--   A forcing is **permitted at level** $\nu$ when it is measurable and $\|\xi(t)\|\le\nu$ for almost every $t\ge0$.
--
--   The **cell average** of $\xi$ for a mesh $\eta>0$ is $\xi^{(\eta)}_k=\eta^{-1}\int_{k\eta}^{(k+1)\eta}\xi(u)\,du$. The **continuous phase entries** of a trajectory with clock bits $p_i$ are $\theta_0=0$ and
--   $$\theta_{j+1}=\inf\{t\ge\theta_j:\ p_{(j+1)\bmod4}(z(t))\ge9/10\};$$
--   they **exist** when every one of these sets is nonempty. The **Euler phase-entry time** $t^{(\eta)}_j$ is $\eta$ times the $j$-th phase entry index of the constant-mesh-$\eta$ execution whose disturbances are the cell averages of $\xi$. The **piecewise-affine interpolant** of a constant-mesh orbit takes the value $z_k+\frac{t-k\eta}{\eta}(z_{k+1}-z_k)$ at $t\in[k\eta,(k+1)\eta)$.
--
--   **Formalization Note** Integrability of the integrand is part of the definition, because the Bochner integral of a non-integrable function is $0$; for a continuous field and a bounded measurable forcing it holds automatically.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Theorem 1, p.2 (PDF 4–5); Lemma 16, p.19 (PDF 21); Lemma 49 and Corollary 50, pp.37–38 (PDF 39–40); cell averages, proof of Proposition 15, p.47 (PDF 49)

import Definitions.Def_PolyEulerFlow_eulerOrbit

namespace PolyEulerFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The absolutely continuous solution of `ż = f(z) + ξ(t)`, `z(0) = z0`, on `[0, ∞)` (Corollary 50, pp.37–38; Theorem 1, p.2),
as an integral equation. Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…).
**Formalization Note.** The integrand is required to be interval integrable, because a Bochner integral of a non-integrable
function is `0`. For a continuous `f` and a permitted forcing this holds automatically. -/
def IsForcedSolution (f : E → E) (z0 : E) (ξ : ℝ → E) (z : ℝ → E) : Prop :=
  ContinuousOn z (Set.Ici 0) ∧
    ∀ t, 0 ≤ t →
      IntervalIntegrable (fun u => f (z u) + ξ u) MeasureTheory.volume 0 t ∧
        z t = z0 + ∫ u in (0 : ℝ)..t, (f (z u) + ξ u)

/-- A permitted forcing: measurable, with `‖ξ(t)‖ ≤ ν` for almost every `t ≥ 0` (Theorem 1, p.2). -/
def IsPermittedForcing [MeasurableSpace E] (ν : ℝ) (ξ : ℝ → E) : Prop :=
  Measurable ξ ∧ ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))), ‖ξ t‖ ≤ ν

/-- The cell average `ξ^{(η)}_k = η⁻¹ ∫_{kη}^{(k+1)η} ξ` (proof of Proposition 15, p.47; Lemma 16, p.19). -/
noncomputable def cellAverage (ξ : ℝ → E) (η : ℝ) (k : ℕ) : E :=
  η⁻¹ • ∫ u in ((k : ℝ) * η)..(((k : ℝ) + 1) * η), ξ u

/-- The continuous phase entries `θ₀ = 0`, `θ_{j+1} = inf{t ≥ θ_j : p_{j+1}(z(t)) ≥ 9/10}` (Lemma 16, p.19). -/
noncomputable def contPhaseEntry (pv : Fin 4 → E → ℝ) (z : ℝ → E) : ℕ → ℝ
  | 0 => 0
  | j + 1 => sInf {t | contPhaseEntry pv z j ≤ t ∧ AboveThreshold pv (Fin.ofNat 4 (j + 1)) (z t)}

/-- The set defining `θ_{j+1}` is nonempty for every `j`, so no `θ_j` is the `sInf ∅ = 0` of the reals. -/
def ContPhaseEntriesExist (pv : Fin 4 → E → ℝ) (z : ℝ → E) : Prop :=
  ∀ j, {t | contPhaseEntry pv z j ≤ t ∧ AboveThreshold pv (Fin.ofNat 4 (j + 1)) (z t)}.Nonempty

/-- The Euler phase-entry time `t^{(η)}_j = η k^{(η)}_j` of the constant-mesh `η` execution whose disturbances are the cell
averages of `ξ` (Lemma 16, p.19). -/
noncomputable def cellEulerEntryTime (pv : Fin 4 → E → ℝ) (f : E → E) (z0 : E) (ξ : ℝ → E) (j : ℕ) (η : ℝ) : ℝ :=
  η * (phaseEntry pv (eulerOrbit f z0 (fun _ => η) (cellAverage ξ η)) j : ℝ)

/-- The piecewise-affine interpolant of a constant-mesh `η` orbit at physical time `t` (Lemma 49, p.37). -/
noncomputable def eulerInterpolant (z : ℕ → E) (η t : ℝ) : E :=
  z ⌊t / η⌋₊ + ((t - (⌊t / η⌋₊ : ℝ) * η) / η) • (z (⌊t / η⌋₊ + 1) - z ⌊t / η⌋₊)

end PolyEulerFlow


