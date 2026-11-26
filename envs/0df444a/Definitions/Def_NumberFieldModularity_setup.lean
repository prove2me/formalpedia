-- Prove2me | Definitions.Def_NumberFieldModularity_setup
-- name    : NumberFieldModularity_setup
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T21:05:30.57281+00:00
-- url     : https://prove2.me/theorems/178a524e-ab0b-4da5-bbce-ee5bce944069
-- title:
--   Number-field modularity interface
-- statement:
--   Typed interface for the modularity of elliptic curves over number fields (Thorne, *Elliptic Curves and Modularity*, Conjecture 2.5). It records the finite places, the levels (non-zero ideals $\mathfrak{n}$), the cohomology $H^*(Y_1(\mathfrak{n}),\mathbb{Q})$ as $\mathbb{Q}$-vector spaces, the Hecke operators $T_v$, and the Frobenius traces $a_v(E)$. The globality, elliptic-curve, $\mathrm{End}_K(E)=\mathbb{Z}$, cohomology, Hecke and trace conditions are Prop-valued **certification slots** to be connected to concrete definitions in a foundational library; this file provides only the typed interface and does not assert the conjecture.
-- source:
--   Thorne, Elliptic Curves and Modularity, Conjecture 2.5, https://www.dpmms.cam.ac.uk/~jat58/EMS.pdf

import Mathlib
namespace NumberFieldModularity
structure ModularitySetup where
  Place : Type
  Level : Type
  Coh : Level → Type
  [instAdd : ∀ n, AddCommGroup (Coh n)]
  [instMod : ∀ n, Module ℚ (Coh n)]
  hecke : (n : Level) → Place → Coh n →ₗ[ℚ] Coh n
  a : Place → ℚ
  K_isNumberField : Prop
  E_isEllipticCurveOverK : Prop
  End_E_eq_Z : Prop
  coh_is_Y1_cohomology : Prop
  hecke_is_Tv : Prop
  a_is_av : Prop
  K_is_Q : Prop
  K_isRealQuadratic : Prop
attribute [instance] ModularitySetup.instAdd ModularitySetup.instMod
end NumberFieldModularity


