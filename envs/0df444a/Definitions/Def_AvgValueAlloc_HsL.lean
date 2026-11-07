-- Prove2me | Definitions.Def_AvgValueAlloc_HsL
-- name    : AvgValueAlloc_HsL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:36.206225+00:00
-- url     : https://prove2.me/theorems/f0b148b1-b27b-4829-b482-8d708a7311a3
-- title:
--   Retained local funding objective $H^s_L(M,Y)$
-- statement:
--   Under shift $s\in\{0,1\}$ a funding sponsor is **retained** if it is local and all its positive alternatives lie in one shifted group $J_{\ell,s}$ (locality is tested first). Then
--   $$
--   H^s_L(M,Y)=\max\bigl\{W(X)+G^s_Y(B(X)):\ X \text{ a routing of } M \text{ using retained sponsors only}\bigr\}.
--   $$
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.3, p.7; §3.3, p.9

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum

namespace AvgValueAlloc

/-- A funding sponsor retained under shift `s`: it is local and all its positive alternatives lie in
one shifted group `J_{ℓ,s}`. -/
def IsRetained {n : ℕ} (ρ : Fin n → ℚ) (s : ℕ) (v : Vec n) : Prop :=
  IsSponsor ρ v ∧ IsLocal ρ v ∧ ∀ i ∈ posSet ρ v, ∀ j ∈ posSet ρ v, shBand ρ s i = shBand ρ s j

/-- **The shifted objective restricted to retained local funding, `H^s_L(M, Y)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.3, p.7: "Writing H^s_L for the shifted objective
restricted to retained local funding"; §3.3, p.9: "Test locality first, then retain a funding
sponsor only if all its positive alternatives lie in one shifted group. Nonlocal sponsors are
excluded even if they fit such a group"; Lemma 3.4: "Here H^s_L maximizes over retained local
funding routes."

`HsL ρ s M Y = max {W(X) + G^s_Y(B(X))}` over routings `X` of the funding items `M` that route only
retained sponsors.

**Formalization Note.** A real `⨆` over a finite nonempty type (the empty routing qualifies). -/
noncomputable def HsL {n m : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (s : ℕ)
    (M : Fin m → Vec n) (Y : ι → Vec n) : ℝ :=
  ⨆ X : {X : Fin m → Option (Fin n) //
      IsRouting ρ M X ∧ ∀ t, X t ≠ none → IsRetained ρ s (M t)},
    welfare M X.1 + Gsh ρ s Y (routBank ρ M X.1)

end AvgValueAlloc


