-- Prove2me | Definitions.Def_PADMPriv_jointLaw
-- name    : PADMPriv_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:53.621196+00:00
-- url     : https://prove2.me/theorems/ddd0ee42-fbd9-41ff-904b-5f93bc513151
-- title:
--   Joint law of data, noise and stopping time in the utility analysis
-- statement:
--   In the utility analysis the records $d_{(1)},\dots,d_{(n)}$ are i.i.d. $P_R$, the noise vectors $z_{(1)},\dots,z_{(n)}$ are i.i.d. with law $P_z$ and independent of the data, and the stopping time $K$ is uniform on $\{\lfloor n/2\rfloor+1,\dots,n\}$ and independent of both. This is the joint law of $(D,z,K)$:
--   $$
--   P_R^{\otimes n}\otimes P_z^{\otimes n}\otimes \mathrm{Unif}\{\lfloor n/2\rfloor+1,\dots,n\}.
--   $$
--   Expectations of the stopped iterate $\tilde u_{(K)}$ in Theorems 5.2 and 5.4 are taken under it.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 3.3, p.8; A.14, p.30

import Mathlib
import Definitions.Def_PADMPriv_stopLaw

namespace PADMPriv

open MeasureTheory

/-- The joint law of the data, the noise and the stopping time in the utility analysis of
Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d) (Section 3.3, p.8; A.14, p.30): the records `d₍₁₎, …, d₍ₙ₎` are i.i.d.
`P_R`, the noise vectors `z₍₁₎, …, z₍ₙ₎` are i.i.d. `P_z` and independent of the data, and `K`
is uniform on `{⌊n/2⌋ + 1, …, n}`, independent of both.

**Formalization Note** The product measure `(P_R^{⊗n} ⊗ P_z^{⊗n}) ⊗ Unif(stopWindow n)` on
`((Fin n → R) × (Fin n → ℝᵐ)) × ℕ`. -/
noncomputable def jointLaw {m : ℕ} {R : Type*} [MeasurableSpace R] (n : ℕ) (PR : Measure R)
    [SigmaFinite PR] (Pz : Measure (EuclideanSpace ℝ (Fin m))) [SigmaFinite Pz] :
    Measure (((Fin n → R) × (Fin n → EuclideanSpace ℝ (Fin m))) × ℕ) :=
  ((Measure.pi fun _ : Fin n => PR).prod (Measure.pi fun _ : Fin n => Pz)).prod (stopLaw n)

end PADMPriv


