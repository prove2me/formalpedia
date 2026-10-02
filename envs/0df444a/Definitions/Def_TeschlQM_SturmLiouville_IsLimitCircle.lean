-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
-- name    : TeschlQM_SturmLiouville_IsLimitCircle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:44:05.498989+00:00
-- url     : https://prove2.me/theorems/a0c101c7-2473-4904-bc54-4156e496ebaf
-- title:
--   Limit circle and limit point endpoints
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. The expression $\tau$ is **limit circle** (l.c.) at $a$ if there is a $v \in \mathfrak{D}(\tau)$ with
--   $$W_a(v^*, v) = 0 \quad\text{such that}\quad W_a(v, f) \neq 0 \text{ for at least one } f \in \mathfrak{D}(\tau).$$
--   Otherwise $\tau$ is **limit point** (l.p.) at $a$. The same definitions with $W_b$ give l.c. and l.p. at $b$. Here $v^*$ is the complex conjugate function.
--
--   This Wronskian definition is the one of p. 187; that it is equivalent to square integrability of all solutions near the endpoint is Weyl's alternative (Theorem 9.9), which is therefore not built into the definition.
--
--   **Formalization Note.** `IsLimitCircleLeft L` and `IsLimitCircleRight L`; limit point is their negation.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 187, Section 9.2

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

namespace TeschlQM.SturmLiouville

/-- Teschl, p. 187: `τ` is *limit circle* (l.c.) at `a` if there is a `v ∈ D(τ)` with
`W_a(v*, v) = 0` such that `W_a(v, f) ≠ 0` for at least one `f ∈ D(τ)`. Here `v* = conj ∘ v`.
Otherwise `τ` is *limit point* (l.p.) at `a`, i.e. `¬ IsLimitCircleLeft L`. -/
def IsLimitCircleLeft (L : SLData) : Prop :=
  ∃ v : ℝ → ℂ, InMaxDomain L v ∧
    wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
    ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0

/-- Teschl, p. 187: `τ` is limit circle at `b` ("similarly for `b`"). Otherwise it is limit point
at `b`. -/
def IsLimitCircleRight (L : SLData) : Prop :=
  ∃ v : ℝ → ℂ, InMaxDomain L v ∧
    wronskianRight L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
    ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L v f ≠ 0

end TeschlQM.SturmLiouville


