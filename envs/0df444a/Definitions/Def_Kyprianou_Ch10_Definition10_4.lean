-- Prove2me | Definitions.Def_Kyprianou_Ch10_Definition10_4
-- name    : Kyprianou_Ch10_Definition10_4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:40:43.376412+00:00
-- url     : https://prove2.me/theorems/9203f34a-15df-496a-819f-1bee7a642c2c
-- title:
--   Definition 10.4: subcritical, critical and supercritical branching mechanisms
-- statement:
--   Source Definition 10.4 classifies continuous-state branching mechanisms by the sign of the right derivative at the origin, including an infinite negative slope.

import Definitions.Def_Kyprianou_Ch10_DraftSourceBundle
set_option autoImplicit false

namespace Kyprianou.Ch10.Draft

/-- Source Definition 10.4(i): right slope is strictly positive. -/
def def10_4_subcritical (psi : Kyprianou.Ch10.Mechanism) : Prop :=
  Kyprianou.Ch10.SubcriticalMechanism psi

/-- Source Definition 10.4(ii): right slope is exactly zero. -/
def def10_4_critical (psi : Kyprianou.Ch10.Mechanism) : Prop :=
  Kyprianou.Ch10.CriticalMechanism psi

/-- Source Definition 10.4(iii): right slope is strictly negative. -/
def def10_4_supercritical (psi : Kyprianou.Ch10.Mechanism) : Prop :=
  Kyprianou.Ch10.SupercriticalMechanism psi

end Kyprianou.Ch10.Draft


