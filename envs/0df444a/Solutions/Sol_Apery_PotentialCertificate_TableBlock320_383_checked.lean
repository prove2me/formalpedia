-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock320_383.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:11:01.769676+00:00
-- url     : https://prove2.me/submissions/7c3eae7b-a167-4ffc-8f7e-d0ea6691538f

import Definitions.Def_Zeta5_PotentialTableBlock320_383Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock320_383.certificate.Valid := by decide +kernel

#print axioms solution
