-- Prove2me | Definitions.Def_TaoFivePrimes_RH101To102TranslationCertificate
-- name    : TaoFivePrimes_RH101To102TranslationCertificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T04:20:39.155977+00:00
-- url     : https://prove2.me/theorems/13323060-f670-461c-97c6-18788a3104c7
-- title:
--   RH local translation certificate at height 101.5
-- statement:
--   The proposed 32 rounded local Taylor coefficients at height 101.5, bundled with an ordinary Lean kernel proof of every exact integer translation residual inequality against the accepted proposed Mellin moments. The common denominator is 8*10^64*2^4096. These explicitly noncomputable certificate data prove only finite integer inequalities; the separate analytic error and RH proofs remain necessary.
-- source:
--   sometik179's original theta/Mellin and polynomial method, c9908072-d99a-4431-aad8-a72c6352619a; ordinary-syntax pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a and accepted moment enclosure c8862379-7ebd-45e7-8271-314543d5c71e. Theta/Mellin foundations attributed to Gabewhigham. New exact integer translations of the public proposed moments, with ordinary Lean validity proofs. This dependent data representation follows the accepted finite moment packets, and asserts no analytic enclosure or RH conclusion on its own.

/- Exact integer translation of the accepted proposed Mellin moments.
Original analytic method and moments: sometik179; theta/Mellin: Gabewhigham.
The finite validity fields are ordinary Lean kernel proofs. This data alone
asserts no analytic coefficient enclosure or RH theorem. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHLocalTranslationArithmetic
open Finset
noncomputable def denominator : ℕ := 8*10^64*2^4096
noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n ≤ k then k.factorial/(n.factorial*(k-n).factorial) else 0
noncomputable def numerator (p : ℤ) (S n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^4096:ℤ) else 0)*(S:ℤ)-
  (S:ℤ)*∑ j ∈ range 256,
    TaoFivePrimes_RH14To100RoundedMomentData.getD j 0*(-1:ℤ)^j*
    ((2^(4096-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*p^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*p^(2*j-n))
noncomputable def Valid (p : ℤ) (S N : ℕ) (cs : List ℤ) : Prop :=
  ∀ n : Fin N, |(10^8:ℤ)*numerator p S n-cs.getD n 0*(denominator:ℤ)| ≤ (denominator:ℤ)
noncomputable instance (p : ℤ) (S N : ℕ) (cs : List ℤ) : Decidable (Valid p S N cs) :=
  inferInstanceAs (Decidable (∀ n : Fin N, _ ≤ _))
end RHLocalTranslationArithmetic
noncomputable def TaoFivePrimes_RH101To102TranslationCertificate : { cs : List ℤ // RHLocalTranslationArithmetic.Valid 203 (10^33) 32 cs } :=
  ⟨[4866968715, 22013961324, -25022939073, 5053576357, 2992204322, -1551557643, 160404139, 53205217, -16609352, 915159, 315029, -62270, 1777, 773, -104, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide +kernel⟩


