-- Prove2me | Definitions.Def_HuangN13_SpecialJetCodeCore
-- name    : HuangN13_SpecialJetCodeCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:05:43.233995+00:00
-- url     : https://prove2.me/theorems/ffc0b0af-2c92-4500-b1ee-81f2947a9837
-- title:
--   Six branch jet orders and their weighted degree-four code
-- statement:
--   The original order of the first nonzero coefficient below nine in each of the six fixed branch polynomials, together with their weighted combination in ZMod19.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; no original-file line mapping is asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false

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
def sixJetOrders (a : Fin 5 → K) (b : Fin 2 → K) (i : Fin 6) : ℕ :=
  jetOrder (sixJetPolynomials a b i)
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
def weightedJetCode (a : Fin 5 → K) (b : Fin 2 → K) : ZMod 19 :=
  (sixJetOrders a b 0 : ZMod 19) - sixJetOrders a b 1 +
    7 * (sixJetOrders a b 2 : ZMod 19) - 7 * sixJetOrders a b 3 +
    8 * (sixJetOrders a b 4 : ZMod 19) - 8 * sixJetOrders a b 5
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


