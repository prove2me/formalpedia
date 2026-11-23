-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:23.387807+00:00
-- url     : https://prove2.me/theorems/bfe0ad4c-c0b1-402f-8bd1-e3894b32723a
-- title:
--   Chart WD
-- statement:
--   Definitions and structural lemmas for Chart WD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
section Charts
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
abbrev locM (K : Type) [Field K] {S : Type} [CommRing S] [Algebra K S] (m : Ideal S) [m.IsPrime] :
    S →ₐ[K] Localization.AtPrime m :=
  IsScalarTower.toAlgHom K S (Localization.AtPrime m)
def FrChartAt {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] (A : TRing K)
    (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (a : A.R →ₐ[K] p'.R) (μ : p'.R →ₐ[K] Localization.AtPrime m)
      (y' : pts p'.R), mapR lam y y' ∧ mapR a u y' ∧ μ.comp lam = (locM K m).comp φ ∧ μ.comp a = c
def FrChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m), FrChartAt pts mapR w m A u c
def BorChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
    ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m) (B : TRing K) (uB uB' : pts B.R)
        (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R) (cB : B.R →ₐ[K] Localization.AtPrime m),
        FrChartAt pts mapR w m A u c ∧ FrChartAt pts mapR w' m A u c' ∧ mapR π u uB ∧ mapR π' u uB' ∧
          borR tB uB uB' ∧ cB.comp π = c ∧ cB.comp π' = c' ∧ ∀ i, cB (tB i : B.R) = locM K m (t i : S)
variable {pts mapR borR}
end Charts
end Formalism.L2.Pj


