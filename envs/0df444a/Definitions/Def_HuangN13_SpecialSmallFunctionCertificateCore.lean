-- Prove2me | Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
-- name    : HuangN13_SpecialSmallFunctionCertificateCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:06:26.460095+00:00
-- url     : https://prove2.me/theorems/49451b26-a7ef-4548-a12b-510f1c37e8bc
-- title:
--   Six-jet certificate data for the N13 reduction
-- statement:
--   For coefficient vectors a in F₂⁵ and b in F₂², form the affine numerator and ordinate, their infinity-chart forms, and the six prescribed local jet polynomials. PairCertificate says that norm support dividing X¹⁶(X−1)¹⁶ forces each jet to have a first nonzero coefficient before degree9 and their prescribed weighted order sum to vanish modulo19.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean; exact flattened source declaration ranges and hashes are recorded alongside this payload. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def numerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (i : ℕ)
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def ordinate (b : Fin 2 → K) : K[X] := C (b 0) + C (b 1) * X
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def infinityNumerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (4 - (i : ℕ))
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def infinityOrdinate (b : Fin 2 → K) : K[X] := C (b 0) * X + C (b 1)
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def sixJetPolynomials (a : Fin 5 → K) (b : Fin 2 → K) : Fin 6 → K[X] := ![
  numerator a + ordinate b * jetZeroZero,
  numerator a + ordinate b * jetZeroOne,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneZero,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneOne,
  infinityNumerator a + infinityOrdinate b * jetInfinityZero,
  infinityNumerator a + infinityOrdinate b * jetInfinityOne]
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def PairCertificate (a : Fin 5 → K) (b : Fin 2 → K) : Prop :=
  N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
    (X : K[X]) ^ 16 * (X - 1) ^ 16 → GoodJets (sixJetPolynomials a b)
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end


