-- Prove2me | Definitions.Def_QseriesFormalization_DefMod7
-- name    : QseriesFormalization_DefMod7
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-23T08:30:28.57012+00:00
-- url     : https://prove2.me/theorems/6a138e67-0db9-4bf9-99ee-574591e94322
-- title:
--   Residue sections modulo 7 and squared dissection components
-- statement:
--   Let $R$ be a commutative ring, $r\in\mathbb{N}$, and $\varphi\in R[[X]]$. The definitions include the uncompressed section by $$[X^n]\operatorname{section7}(R,r,\varphi)=\begin{cases}[X^n]\varphi,&n\bmod7=r,\\0,&n\bmod7\ne r,\end{cases}$$ for every $n\in\mathbb{N}$. The predicate $\operatorname{IsRes7}(r,\varphi)$ means that $[X^n]\varphi=0$ whenever $n\bmod7\ne r$. Thus $r\ge7$ gives a zero section and forces a supported series to be zero. Over $(\mathbb{Z}/7\mathbb{Z})[[X]]$, it defines $\operatorname{ASD}_7(r)$ as this section of $E(X)^3$, where $E$ is `qPochInfPS`. These support the congruence $p(7n+5)\equiv0\pmod7$.
--
--   The definitions include, in $(\mathbb{Z}/7)[[X]]$, $Q_7=(q;q)_\infty$, $D_7=(q^7;q^7)_\infty$, $P_7=\sum p(n)X^n$, and $S_7=\mathrm{ASD}_7(0)+\mathrm{ASD}_7(1)+\mathrm{ASD}_7(3)$. It also defines the six square-expansion terms $N_0=\mathrm{ASD}_7(0)^2$, $N_1=2\,\mathrm{ASD}_7(0)\mathrm{ASD}_7(1)$, $N_2=\mathrm{ASD}_7(1)^2$, $N_3=2\,\mathrm{ASD}_7(0)\mathrm{ASD}_7(3)$, $N_4=2\,\mathrm{ASD}_7(1)\mathrm{ASD}_7(3)$ and $N_6=\mathrm{ASD}_7(3)^2$ appearing in $S_7^2$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod7.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).

-- Definition group: QseriesFormalization_DefMod7; exact rendered source bodies in isolated sections.
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

-- Source module: QseriesFormalization.Pending.Chapter17_ASD_Mod7
section

/-!
# Chapter 17 — Atkin-Swinnerton-Dyer dissection mod 7

This file records the mod-7 residue decomposition of the Jacobi cube
`(qPochInfPS (ZMod 7))^3` used in Hirschhorn §3.7.
-/

namespace QseriesFormalization
namespace Pending
namespace Hirschhorn7

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- The 7-residue section of a formal power series over `R`: keep only
coefficients at indices congruent to `r` modulo 7. -/
noncomputable def section7 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 7 = r then φ.coeff n else 0)

/-- A formal power series is supported on one residue class modulo 7. -/
def IsRes7 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 7 ≠ r → φ.coeff n = 0

/-- The `r`-th residue component of `(qPochInfPS (ZMod 7))^3`. -/
noncomputable def ASD7 (r : ℕ) : (ZMod 7)⟦X⟧ :=
  section7 (ZMod 7) r ((qPochInfPS (ZMod 7))^3)


end Hirschhorn7
end Pending
end QseriesFormalization

end

-- Source module: QseriesFormalization.Pending.Chapter17_ASD_Mod7_Full
section

/-!
# Chapter 17 — Full mod-7 ASD residue extraction

This file continues `Pending.Chapter17_ASD_Mod7`.  It keeps the
Atkin--Swinnerton-Dyer mod-7 dissection in terms of the already-proved section
components

* `ASD7 0`, the residue-0 component of `(q;q)_∞^3`;
* `ASD7 1`, the residue-1 component of `(q;q)_∞^3`;
* `ASD7 3`, the residue-3 component of `(q;q)_∞^3`.

After Frobenius, the denominator-cleared form of Hirschhorn §3.7 is

`partitionGenFun * expand 7 qPochInfPS = (ASD7 0 + ASD7 1 + ASD7 3)^2`

in `(ZMod 7)⟦X⟧`.  Applying the compressed `7`-section operator gives the
seven generating-function congruences, with the right-hand side still written
in section-component form.  The residue-5 section vanishes.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDMod7Full

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Hirschhorn7

noncomputable abbrev Q7 : (ZMod 7)⟦X⟧ :=
  qPochInfPS (ZMod 7)

noncomputable abbrev D7 : (ZMod 7)⟦X⟧ :=
  PowerSeries.expand 7 (by decide) Q7

noncomputable abbrev P7 : (ZMod 7)⟦X⟧ :=
  partitionGenFun (ZMod 7)

noncomputable abbrev S7 : (ZMod 7)⟦X⟧ :=
  ASD7 0 + ASD7 1 + ASD7 3

noncomputable abbrev N0 : (ZMod 7)⟦X⟧ :=
  (ASD7 0) ^ 2

noncomputable abbrev N1 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 0 * ASD7 1

noncomputable abbrev N2 : (ZMod 7)⟦X⟧ :=
  (ASD7 1) ^ 2

noncomputable abbrev N3 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 0 * ASD7 3

noncomputable abbrev N4 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 1 * ASD7 3

noncomputable abbrev N6 : (ZMod 7)⟦X⟧ :=
  (ASD7 3) ^ 2

end ASDMod7Full
end Pending
end QseriesFormalization

end


