-- Prove2me | Definitions.Def_SupplierLearning_SupplierType
-- name    : SupplierLearning_SupplierType
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:38.931354+00:00
-- url     : https://prove2.me/theorems/35a0d02a-7851-441b-8021-01019d4f03b0
-- title:
--   Supplier types $\theta\in\{\ell,h\}$
-- statement:
--   The supplier has one of two types $\theta\in\{\ell,h\}$: type $\ell$ has the lower unit cost, type $h$ the higher one. The type is the supplier's private information in regime $\mathcal P^{\mathrm{AL}}$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.5

import Mathlib

namespace SupplierLearning

/-- **Supplier types θ∈{ℓ,h}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.5 (PDF p.5).

**Formalization Note.** `l` is the low-cost type ℓ, `h` the high-cost type. -/
inductive SupplierType where
  | l
  | h
  deriving DecidableEq

end SupplierLearning


