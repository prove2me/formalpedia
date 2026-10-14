-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock384_447.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:11:55.908843+00:00
-- url     : https://prove2.me/submissions/de814038-9a69-491b-9f83-19aa20cbc713

import Definitions.Def_Zeta5_PotentialTableBlock384_447Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock384_447.certificate.Valid := by decide +kernel

#print axioms solution
