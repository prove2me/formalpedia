-- Prove2me | Definitions.Def_QPVEntanglement_Geometry
-- name    : QPVEntanglement_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:26:40.089553+00:00
-- url     : https://prove2.me/theorems/03f42b60-831c-47d2-a484-f54e8cd41ba5
-- title:
--   One-dimensional static-verifier geometry
-- statement:
--   A **geometry** consists of the positions $v_0, v_1\in\mathbb R$ of the two verifiers $V_0, V_1$ and a claimed location $x\in\mathbb R$ that is **admissible**: it lies in the convex hull of $\{v_0,v_1\}$ and is not one of them, i.e. $\min(v_0,v_1)<x<\max(v_0,v_1)$. $V_0$ is the sender of every BB84 state. Write $d_b=|x-v_b|$, $D=\max(d_0,d_1)$ and $\ell_{01}=|v_1-v_0|$. Signals travel at speed $1$.
--
--   This is the setting of every protocol-level statement of the mission.
--
--   **Formalization Note** The geometry is arbitrary; the paper's normalization (claimed location $0$, $V_0=-L$, $V_1=R$, p.36) is not imposed.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Definition 2, p.28; §7 Notations for the Proof, p.36

import Mathlib

set_option autoImplicit false

namespace QPVEntanglement

/-- **One-dimensional static-verifier geometry** (Definition 2, p.28; "Notations for the Proof",
p.36). Behera–Goyal, *Breaking the Bounded Entanglement Barrier for Quantum Position
Verification*, arXiv:2609.39234 (sha256 bdf2928d…), Definition 2, p.28.

`v 0` is the position of the verifier `V₀` (the sender of every BB84 state) and `v 1` that of
`V₁`; `x` is the claimed location. It is *admissible*: it lies in the convex hull of the
verifier positions and is not one of them, i.e. strictly between them.

**Formalization Note.** Pinned model P1 (BRIEF): the theorem is stated for arbitrary real
`v 0, v 1, x` instead of translating `x` to `0` and reflecting (p.36 does both "without loss of
generality"). Speed of light is `1` ("No information or physical system travels faster than
speed 1", p.29). -/
structure Geometry where
  /-- verifier positions: `v 0` is `V₀`, `v 1` is `V₁` -/
  v : Fin 2 → ℝ
  /-- the claimed location -/
  x : ℝ
  /-- admissibility in one dimension: `x ∈ Conv(v 0, v 1) \ {v 0, v 1}` -/
  admissible : min (v 0) (v 1) < x ∧ x < max (v 0) (v 1)

namespace Geometry

/-- `d b = |x − v b|`, the distance from the claimed location to `V_b` (p.36: `d₀ = L`,
`d₁ = R`). -/
noncomputable def d (G : Geometry) (b : Fin 2) : ℝ := |G.x - G.v b|

/-- `D = max(d₀, d₁)` (p.36, p.37). -/
noncomputable def D (G : Geometry) : ℝ := max (G.d 0) (G.d 1)

/-- `ℓ₀₁ = |v₁ − v₀|`, the distance between the verifiers (equal to `d₀ + d₁`). -/
noncomputable def len (G : Geometry) : ℝ := |G.v 1 - G.v 0|

/-- `p` lies on the closed segment between the two verifiers. -/
def OnSegment (G : Geometry) (p : ℝ) : Prop := min (G.v 0) (G.v 1) ≤ p ∧ p ≤ max (G.v 0) (G.v 1)

end Geometry

end QPVEntanglement


