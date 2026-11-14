-- Prove2me | Definitions.Def_CatalyticTreeEval_CRT
-- name    : CatalyticTreeEval_CRT
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:43:03.389845+00:00
-- url     : https://prove2.me/theorems/dda4a2a1-8a75-47a9-bf78-f012bacf01db
-- title:
--   CRT projections and reconstruction for distinct prime moduli
-- statement:
--   Residue projections from the product modulus to each prime component, and reconstruction by the bounded Chinese remainder representative. The interface is shared by the weight-detector and canonical-decoder constructions; right-inverse and injectivity properties are proved separately.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Lemma3.19 and Appendix B. Uses Mathlib Chinese remainder reconstruction.

import Definitions.Def_CatalyticTreeEval_Main_Matching
import Mathlib.Data.Nat.ChineseRemainder

set_option autoImplicit false

namespace CatalyticTreeEval.CRT

/-- The natural projection from the composite ring to one prime component. -/
def project {t : ℕ} (p : Fin t → ℕ) (i : Fin t) :
    ZMod (Main.modulus p) →+* ZMod (p i) :=
  ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) _

/-- A bounded CRT representative, using Mathlib's finite-set Chinese remainder
construction. The prime-data certificate supplies pairwise coprimality. -/
noncomputable def crtRepresentative {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (y : (i : Fin t) → ZMod (p i)) :
    {n : ℕ // ∀ i ∈ (Finset.univ : Finset (Fin t)), n ≡ (y i).val [MOD p i]} :=
  Nat.chineseRemainderOfFinset (fun i => (y i).val) p Finset.univ
    (fun i _ => (hp.2.1 i).ne_zero)
    (fun i _ j _ hij => (Nat.coprime_primes (hp.2.1 i) (hp.2.1 j)).2
      (fun h => hij (hp.2.2 h)))

/-- CRT lift to the ring whose modulus is the product of the given primes. -/
noncomputable def crtLift {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (y : (i : Fin t) → ZMod (p i)) : ZMod (Main.modulus p) :=
  ((crtRepresentative p hp y).val : ZMod (Main.modulus p))

end CatalyticTreeEval.CRT


