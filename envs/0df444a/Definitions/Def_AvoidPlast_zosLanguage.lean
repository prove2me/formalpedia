-- Prove2me | Definitions.Def_AvoidPlast_zosLanguage
-- name    : AvoidPlast_zosLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:48:56.875913+00:00
-- url     : https://prove2.me/theorems/b823b251-bf49-48ac-8665-146abce4aa4e
-- title:
--   The zero-on-subcube pair language
-- statement:
--   The pair language of Theorem 4.5:
--
--   $$\{((|F|,m,d,|H|),f):f\in\mathrm{ZoS}(F,m,d,H)\},$$
--
--   with $f$ represented by its truth table, $H$ the first $|H|$ elements of $F$ and the integers in binary, for positive $m$, $d$ and $|H|\le|F|$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib
import Definitions.Def_AvoidPlast_ZoS
import Definitions.Def_AvoidPlast_FieldScheme
import Definitions.Def_AvoidPlast_truthTable
import Definitions.Def_AvoidPlast_encZoS

namespace AvoidPlast

/-- The pair language of Theorem 4.5 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.18): `{((|F|, m, d, |H|), f) : f ∈ ZoS(F, m, d, H)}`,
with `f` represented by its truth table and `H` the first `|H|` elements of `F`, for positive `m`, `d`
and a set `H ⊆ F`. -/
def zosLanguage (S : FieldScheme) (x f : List Bool) : Prop :=
  ∃ (Q m d h : ℕ) (hQ : Q ∈ S.sizes), 0 < m ∧ 0 < d ∧ h ≤ Q ∧ x = encZoS Q m d h ∧
    ∃ g : (Fin m → Fin Q) → Fin Q,
      g ∈ @ZoS (Fin Q) (S.field Q hQ) m d {a | a.val < h} ∧ f = truthTable g

end AvoidPlast


