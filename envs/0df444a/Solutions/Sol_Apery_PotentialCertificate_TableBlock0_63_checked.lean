-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock0_63.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:09:33.968903+00:00
-- url     : https://prove2.me/submissions/f48a9b1a-a264-48ea-8751-2cbaaf718c3f

import Definitions.Def_Zeta5_PotentialTableBlock0_63Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock0_63.certificate.Valid := by decide +kernel

#print axioms solution
