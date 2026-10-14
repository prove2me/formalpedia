-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock128_191.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:10:04.668062+00:00
-- url     : https://prove2.me/submissions/95adf433-8b11-464c-ad14-af48ef2f50c0

import Definitions.Def_Zeta5_PotentialTableBlock128_191Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock128_191.certificate.Valid := by decide +kernel

#print axioms solution
