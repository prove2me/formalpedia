-- Prove2me | Definitions.Def_OWFLocalDesc_IsOWF
-- name    : OWFLocalDesc_IsOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:55.214651+00:00
-- url     : https://prove2.me/theorems/5773ac81-7109-4787-a5c5-b21161e9b4ab
-- title:
--   One-way function (Definition 2.7)
-- statement:
--   Let $f:\{0,1\}^*\to\{0,1\}^*$ be computable in deterministic polynomial time. In the **inversion experiment** at length $n$, a string $u$ is drawn uniformly from $\{0,1\}^n$ and an inverter $I$ receives $(1^n, f(u))$; it **succeeds** if it outputs a string $v$ with $f(v)=f(u)$. Write
--   $$\mathrm{Inv}_f(I,n)=\Pr_{u\sim U_n,\ I}\big[f(I(1^n,f(u)))=f(u)\big].$$
--   The function $f$ is **one-way** if $\mathrm{Inv}_f(I,\cdot)$ is negligible for every PPT inverter $I$.
--
--   **Formalization Note** The helper `invSuccess f I n` is $\mathrm{Inv}_f(I,n)$. The inverter's output may have any length; only $f(v)=f(u)$ is checked.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_OWFLocalDesc_Negligible
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Inversion success.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14: "the inversion
experiment draws u uniformly from {0,1}^n and gives the inverter (1^n, f(u)). The inverter succeeds
if it outputs a string v with f(v) = f(u)."

`invSuccess f I n` is the probability, over a uniform `u ∈ {0,1}ⁿ` and the coins of `I`, that
`I` on input `tupleCode [1ⁿ, f(u)]` outputs a string `v` (of any length) with `f v = f u`. -/
noncomputable def invSuccess (f : List Bool → List Bool) (I : PPT) (n : ℕ) : ℝ :=
  (∑ u : Fin n → Bool, I.prob (QuantumPRC.tupleCode [QuantumPRC.unary n, f (List.ofFn u)])
      (fun v => f v = f (List.ofFn u))) / (2 : ℝ) ^ n

/-- **One-way function (Definition 2.7).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14:
"For a deterministic polynomial-time function f, … A one-way function is such a function whose
inversion success is negligible for every PPT inverter."

**Formalization Note.** `f` is one function on all binary strings, polynomial-time in the
published one-tape model; the inverter's output is not required to have any particular length. -/
def IsOWF (f : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable f ∧ ∀ I : PPT, Negligible (invSuccess f I)

end OWFLocalDesc


