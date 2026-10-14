-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock512_575.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:13:20.021426+00:00
-- url     : https://prove2.me/submissions/a5e71a4b-9cc1-4fae-9ef1-846058c97469

import Definitions.Def_Zeta5_PotentialTableBlock512_575Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock512_575.certificate.Valid := by decide +kernel

#print axioms solution
