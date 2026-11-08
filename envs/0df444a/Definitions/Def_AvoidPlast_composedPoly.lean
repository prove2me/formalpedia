-- Prove2me | Definitions.Def_AvoidPlast_composedPoly
-- name    : AvoidPlast_composedPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:40.285205+00:00
-- url     : https://prove2.me/theorems/78fa5606-f482-43bb-bf55-bf519d2eeeb6
-- title:
--   The composed polynomial $\tilde p$
-- statement:
--   The polynomial of Eq. (4.1): $\tilde p(z)=\tilde x(\tilde y_1(z),\dots,\tilde y_{m_1}(z))-\tilde y_{m_1+1}(z)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Eq. (4.1), p.19

import Mathlib

namespace AvoidPlast

/-- The polynomial `p̃(z) = x̃(ỹ₁(z), …, ỹ_{m₁}(z)) − ỹ_{m₁+1}(z)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Eq. (4.1), p.19). -/
def composedPoly {F : Type} [Field F] {m₁ m₂ : ℕ} (xt : (Fin m₁ → F) → F)
    (y : Fin (m₁ + 1) → (Fin m₂ → F) → F) (z : Fin m₂ → F) : F :=
  xt (fun i => y i.castSucc z) - y (Fin.last m₁) z

end AvoidPlast


