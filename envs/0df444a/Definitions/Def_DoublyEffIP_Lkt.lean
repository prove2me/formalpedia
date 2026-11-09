-- Prove2me | Definitions.Def_DoublyEffIP_Lkt
-- name    : DoublyEffIP_Lkt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:20.203198+00:00
-- url     : https://prove2.me/theorems/46c75169-da13-4793-9b44-7d8ba0f4e783
-- title:
--   The batch language $L^k_t$
-- statement:
--   For an index set $I$, the **batch language** $L^I_t$ consists of the batches $x=((x_{i,\mathrm{start}},x_{i,\mathrm{end}}))_{i\in I}$ of transition claims that are all correct:
--
--   $$
--   L^I_t=\{x \mid \forall i\in I,\ (x_{i,\mathrm{start}},x_{i,\mathrm{end}})\in L_t\}.
--   $$
--
--   The paper's $L^k_t$ is $I=[k]$; the expanded batch of $k\lambda$ sub-transitions is indexed by $I=[k]\times[\lambda]$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4, p.14; Table 1, p.20

import Mathlib
import Definitions.Def_DoublyEffIP_Lt

set_option autoImplicit false

namespace DoublyEffIP

/-- **The batch language `L^k_t`** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient
IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4, p.14:
`L^k_t := {((x_{i,start}, x_{i,end}))_{i∈[k]} | ∀ i ∈ [k] (x_{i,start}, x_{i,end}) ∈ L_t}`.

`Lkt step t ι` is the set of batches `x : ι → C × C` of transition claims, all in `L_t`.

**Formalization Note.** The batch is indexed by an arbitrary type `ι`: `L^k_t` is `ι = Fin k`, and
the expanded batch `x^↖` of size `kλ` (p.20, Table 1) is indexed by `Fin k × Fin λ`. -/
def Lkt {C : Type*} (step : C → C) (t : ℕ) (ι : Type*) : Set (ι → C × C) :=
  {x | ∀ i, x i ∈ Lt step t}

end DoublyEffIP


