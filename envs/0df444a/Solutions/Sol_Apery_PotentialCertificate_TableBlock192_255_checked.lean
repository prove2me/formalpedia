-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock192_255.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:10:05.557809+00:00
-- url     : https://prove2.me/submissions/42cd5f2b-7f03-491c-82c3-157b46e554ec

import Definitions.Def_Zeta5_PotentialTableBlock192_255Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock192_255.certificate.Valid := by decide +kernel

#print axioms solution
