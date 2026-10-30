-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_Charges
-- name    : CachonFisherInventory_LowerBound_Charges
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:47:57.688287+00:00
-- url     : https://prove2.me/theorems/7c6b6bbd-ccc3-4dcf-853e-b4335ed0295f
-- title:
--   Retailer and supplier charges, residue average, and printed critical point
-- statement:
--   Write x⁺=max(x,0) and x⁻=max(−x,0). For an integer inventory position y, define Ḡ_r(y)=E[h_r(y−D^{L_r+1})⁺+(h_s+p_r)(y−D^{L_r+1})⁻]. This expectation is computed as a finite sum over all L_r+1 independent demand coordinates, with product probabilities. For y≤R define a_R(y)=y+Q_r(⌊(R−y)/Q_r⌋+1), the strictly next point above R in y's residue class. Let G_p(y,R)=Ḡ_r(y)−Ḡ_r(a_R(y)) for y≤R, and zero otherwise. Put G_r(y,R)=Ḡ_r(y)−G_p(y,R) and G_s(y,IP,R)=h_s(y−Nμ_r)+Σ_i G_p(IP_i,R).
--
--   The printed critical-point predicate says that R is the greatest integer in {r : Ḡ_r(r+Q_r)≤Ḡ_r(r)}. It neither chooses a default nor assumes such an integer exists. C_r(R)=Q_r⁻¹ Σ_{c=1}^{Q_r} Ḡ_r(R+c), including every residue. No uniform-occupation or optimality assertion is part of the definition.
--
--   For safe integration, K(R)=Σ_{c=1}^{Q_r}Ḡ_r(R+c) and b(R)=−h_s Nμ_r−N[h_s(|R|+1)+K(R)] are explicit real numbers. Whenever Σ_i IP_i≤y, the formulas imply G_s(y,IP,R)≥b(R); this lower bound is not a structure field or a hypothesis. It is an integration offset only, and is not C̲_s. The statement audit records the elementary bound behind its use.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.1, p. 1039 (PDF p. 8); §5.2, p. 1040 (PDF p. 9)

import Definitions.Def_CachonFisherInventory_LowerBound_Parameters

namespace CachonFisherInventory.LowerBound

/-- Finite expectation over Lr+1 independent bounded demands, §5.1. -/
noncomputable def baseCharge (P : Parameters) (y : ℤ) : ℝ :=
  ∑ d : Fin (P.Lr + 1) → Fin (P.dbar + 1),
    (∏ k, (P.law (d k)).toReal) *
      (P.hr * max ((y : ℝ) - ∑ k, ((d k).val : ℝ)) 0 +
       (P.hs + P.pr) * max ((∑ k, ((d k).val : ℝ)) - y) 0)

/-- The strictly next integer above R in the residue class of y. -/
def nextResidue (P : Parameters) (y R : ℤ) : ℤ :=
  y + P.Qr * ((R - y) / P.Qr + 1)

noncomputable def penaltyCharge (P : Parameters) (y R : ℤ) : ℝ :=
  if y ≤ R then baseCharge P y - baseCharge P (nextResidue P y R) else 0

noncomputable def retailerCharge (P : Parameters) (y R : ℤ) : ℝ :=
  baseCharge P y - penaltyCharge P y R

noncomputable def supplierCharge (P : Parameters) (y : ℤ) (ip : Fin P.N → ℤ)
    (R : ℤ) : ℝ :=
  P.hs * ((y : ℝ) - P.N * meanDemand P) + ∑ i, penaltyCharge P (ip i) R

/-- The printed largest-integer specification, with no totalized optimizer. -/
def PrintedCriticalPoint (P : Parameters) (R : ℤ) : Prop :=
  IsGreatest {r : ℤ | baseCharge P (r + P.Qr) ≤ baseCharge P r} R

noncomputable def residueSum (P : Parameters) (R : ℤ) : ℝ :=
  ∑ c : Fin P.Qr, baseCharge P (R + c.val + 1)

noncomputable def retailerLowerValue (P : Parameters) (R : ℤ) : ℝ :=
  residueSum P R / P.Qr

/-- A concrete finite lower bound for Gs when sum ip ≤ y. It is only an integration
offset, not the supplier optimization value. No lower-bound proposition is assumed. -/
noncomputable def chargeFloor (P : Parameters) (R : ℤ) : ℝ :=
  -P.hs * P.N * meanDemand P -
    P.N * (P.hs * (|(R : ℝ)| + 1) + residueSum P R)

end CachonFisherInventory.LowerBound


