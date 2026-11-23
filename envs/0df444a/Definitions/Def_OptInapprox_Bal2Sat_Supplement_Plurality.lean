-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_Plurality
-- name    : OptInapprox_Bal2Sat_Supplement_Plurality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:53:16.911304+00:00
-- url     : https://prove2.me/theorems/562ca1e4-b040-4cb7-9442-1b822c776296
-- title:
--   §4.2 and Theorem 8 — plurality, Gaussian competition and Frieze–Jerrum normalization
-- statement:
--   Plurality returns the least most-frequent symbol in a finite input; ties are broken deterministically and no finite-dimensional balance is imposed. Its vector representation is the corresponding standard-basis vertex.
--
--   Let $(U_i,Z_i)$, $i=0,\ldots,q-1$, be independent copies of the published pair of independent standard Gaussians. Set $V_i=\rho U_i+\sqrt{1-\rho^2}Z_i$ and define
--
--   $$I(q,\rho)=\Pr[\forall i,\ U_i\le U_0\ \text{and}\ V_i\le V_0].$$
--
--   This gives the covariance required in Theorem 8, including singular endpoint laws. The Frieze–Jerrum competition uses the published Gaussian collision probability $P_q(\rho)$ from the k-spokes definition. Its single-colour normalization is $I_{\mathrm{FJ}}(q,\rho)=P_q(\rho)/q$. The bridge between the two laws and this normalization is a conclusion of Theorem 8, not an assumption.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 9,13,29–30, plurality and Theorem 8

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Qary
import Definitions.Def_OptInapprox_Orthant_Setting

namespace OptInapprox.Bal2Sat.Supplement

noncomputable section
open MeasureTheory

/-- Least most-frequent symbol. No finite-n balance is asserted. -/
def plurality {q n : ℕ} (hq : 0 < q) (x : QCube q n) : Fin q :=
  let counts := fun a : Fin q => (Finset.univ.filter (fun i => x i = a)).card
  let m := (Finset.univ : Finset (Fin q)).sup counts
  let winners := (Finset.univ : Finset (Fin q)).filter (fun a => counts a = m)
  winners.min' (by
    have hu : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩, Finset.mem_univ _⟩
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup Finset.univ hu counts
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm⟩⟩)

def pluralityVector {q n : ℕ} (hq : 0 < q) : QCube q n → Fin q → ℝ :=
  fun x => basisVertex (plurality hq x)

/-- q independent pairs of independent standard Gaussians. -/
def contestLaw (q : ℕ) : Measure (Fin q → ℝ × ℝ) :=
  Measure.pi (fun _ => OptInapprox.Orthant.stdGaussPair)

def corrSecond (ρ : ℝ) (p : ℝ × ℝ) : ℝ :=
  ρ * p.1 + Real.sqrt (1 - ρ ^ 2) * p.2

/-- Probability that the first symbol wins both Gaussian competitions. -/
def gaussianContest (q : ℕ) (hq : 0 < q) (ρ : ℝ) : ℝ :=
  (contestLaw q {z | ∀ i : Fin q, (z i).1 ≤ (z ⟨0, hq⟩).1 ∧
    corrSecond ρ (z i) ≤ corrSecond ρ (z ⟨0, hq⟩)}).toReal

/-- The actual Frieze--Jerrum competition, single-colour normalization.
The published collision probability is the sum over q equally likely winning colours. -/
def friezeJerrumI (q : ℕ) (ρ : ℝ) : ℝ :=
  HermiteLaptop.MaxAgree.collisionProb q ρ / q

end
end OptInapprox.Bal2Sat.Supplement


