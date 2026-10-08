-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F07_q00
-- name    : CK_CKLaneM03_Family_F07_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T03:15:47.981858+00:00
-- url     : https://prove2.me/theorems/14696892-79e1-4031-88ef-1c38c40c62c2
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F07 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F07 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F07 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F07 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F07 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneM03_Family_F07_q00_q03

namespace CKLaneM03.EP
open CKLaneM03
namespace P0182
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_50300104205305215202402 (sem_forall_cons l_50300104205305215202403 (sem_forall_cons l_50300104205305215202412 (sem_forall_cons l_50300104205305215202413 (sem_forall_cons l_503001042053052152025024 (sem_forall_cons l_5030010420530521520250250 (sem_forall_cons l_5030010420530521520250251 (sem_forall_cons l_503001042053052152025034 (sem_forall_cons l_503001042053052152025035 (sem_forall_cons l_503001042053052152025124 (sem_forall_cons l_5030010420530521520251250 (sem_forall_cons l_5030010420530521520251251 (sem_forall_cons l_503001042053052152025134 (sem_forall_cons l_5030010420530521520251350 (sem_forall_cons l_5030010420530521520251351 (sem_forall_cons l_50300104205305215203402 (sem_forall_cons l_50300104205305215203403 (sem_forall_cons l_50300104205305215203412 (sem_forall_cons l_50300104205305215203413 (sem_forall_cons l_503001042053052152035024 (sem_forall_cons l_503001042053052152035025 (sem_forall_cons l_50300104205305215203503 (sem_forall_cons l_503001042053052152035124 (sem_forall_cons l_503001042053052152035125 (sem_forall_cons l_503001042053052152035134 (sem_forall_cons l_503001042053052152035135 (sem_forall_cons l_50300104205305215212402 (sem_forall_cons l_50300104205305215212403 (sem_forall_cons l_50300104205305215212412 (sem_forall_cons l_50300104205305215212413 (sem_forall_cons l_503001042053052152125024 (sem_forall_cons l_503001042053052152125034 (sem_forall_cons l_5030010420530521521250350 (sem_forall_cons l_5030010420530521521250351 (sem_forall_cons l_503001042053052152125124 (sem_forall_cons l_503001042053052152125134 (sem_forall_cons l_50300104205305215213402 (sem_forall_cons l_50300104205305215213403 (sem_forall_cons l_50300104205305215213412 (sem_forall_cons l_50300104205305215213413 (sem_forall_cons l_503001042053052152135024 (sem_forall_cons l_5030010420530521521350250 (sem_forall_cons l_5030010420530521521350251 (sem_forall_cons l_503001042053052152135034 (sem_forall_cons l_503001042053052152135035 (sem_forall_cons l_503001042053052152135124 (sem_forall_cons l_5030010420530521521351250 (sem_forall_cons l_5030010420530521521351251 (sem_forall_cons l_503001042053052152135134 (sem_forall_cons l_5030010420530521521351350 (sem_forall_cons l_5030010420530521521351351 (sem_forall_cons l_5030010420530521530420 (sem_forall_cons l_5030010420530521530421 (sem_forall_cons l_5030010420530521530430 (sem_forall_cons l_5030010420530521530431 (sem_forall_cons l_50300104205305215305202 (sem_forall_cons l_50300104205305215305203 (sem_forall_cons l_50300104205305215305212 (sem_forall_cons l_50300104205305215305213 (sem_forall_cons l_50300104205305215305304 (sem_forall_cons l_503001042053052153053052 (sem_forall_cons l_503001042053052153053053 (sem_forall_cons l_50300104205305215305314 (sem_forall_cons l_503001042053052153053152 (sem_forall_cons l_503001042053052153053153 (sem_forall_cons l_50300104205305215314204 (sem_forall_cons l_50300104205305215314205 (sem_forall_cons l_50300104205305215314214 (sem_forall_cons l_50300104205305215314215 (sem_forall_cons l_5030010420530521531430 (sem_forall_cons l_5030010420530521531431 (sem_forall_cons l_503001042053052153152024 (sem_forall_cons l_503001042053052153152025 (sem_forall_cons l_50300104205305215315203 (sem_forall_cons l_503001042053052153152124 (sem_forall_cons l_503001042053052153152125 (sem_forall_cons l_503001042053052153152134 (sem_forall_cons l_503001042053052153152135 (sem_forall_cons l_50300104205305215315304 (sem_forall_cons l_503001042053052153153052 (sem_forall_cons l_503001042053052153153053 (sem_forall_cons l_503001042053052153153142 (sem_forall_cons l_503001042053052153153143 (sem_forall_cons l_503001042053052153153152 (sem_forall_cons l_503001042053052153153153 sem_forall_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0182

namespace P0183

end P0183
end CKLaneM03.EP


