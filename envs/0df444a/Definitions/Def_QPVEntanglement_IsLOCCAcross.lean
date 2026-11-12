-- Prove2me | Definitions.Def_QPVEntanglement_IsLOCCAcross
-- name    : QPVEntanglement_IsLOCCAcross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:19.785451+00:00
-- url     : https://prove2.me/theorems/dd192f43-3e4c-4c21-9655-4ef1beccfe98
-- title:
--   LOCC channels across a bipartition
-- statement:
--   A channel $\Lambda$ from $X\otimes Y$ to $X'\otimes Y'$ is **LOCC across $X:Y$** if, after identifying each register with a standard space by some bijection of basis labels, it is a finite adaptive LOCC protocol: a finite tree of complete local Kraus instruments applied alternately on either side, each continuation depending on the earlier outcomes, with arbitrary intermediate dimensions (the published `FiniteLOCC`).
--
--   It is the class of channels $\Lambda$ in Theorem 6 and Corollaries 1–2.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §3 standard fact (ii), p.26; Theorem 6, p.34

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

set_option autoImplicit false

namespace QPVEntanglement

/-- **An LOCC channel across the cut `X : Y`** (§3 standard fact (ii), p.26; Theorem 6, p.34).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 6, p.34.

`Λ : (X × Y) → (X' × Y')` is LOCC across `X : Y` if, after identifying each register with a
standard `Fin`-indexed space by some bijection of basis labels, it is a finite adaptive LOCC
protocol in the sense of the published `FiniteLOCC` (complete local Kraus instruments on either
side, outcome-dependent continuation, arbitrary intermediate dimensions). -/
def IsLOCCAcross {X Y X' Y' : Type*} (Λ : QAlgorithms.Superop (X × Y) (X' × Y')) : Prop :=
  ∃ (a b c d : ℕ) (eX : X ≃ Fin a) (eY : Y ≃ Fin b) (eX' : X' ≃ Fin c) (eY' : Y' ≃ Fin d)
    (Λ₀ : QAlgorithms.Superop (Fin a × Fin b) (Fin c × Fin d)),
    QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC Λ₀ ∧
    ∀ ρ, Λ ρ = Matrix.reindex (eX'.prodCongr eY').symm (eX'.prodCongr eY').symm
      (Λ₀ (Matrix.reindex (eX.prodCongr eY) (eX.prodCongr eY) ρ))

end QPVEntanglement


