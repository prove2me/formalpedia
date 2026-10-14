-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock64_127.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:10:03.559652+00:00
-- url     : https://prove2.me/submissions/3edd34bc-b86d-4741-8426-6cfe5939e054

import Definitions.Def_Zeta5_PotentialTableBlock64_127Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock64_127.certificate.Valid := by decide +kernel

#print axioms solution
