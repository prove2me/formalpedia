-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock256_319.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:10:20.774297+00:00
-- url     : https://prove2.me/submissions/02acc5e6-fa1c-4921-8ad1-7e7d6cc8e52b

import Definitions.Def_Zeta5_PotentialTableBlock256_319Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock256_319.certificate.Valid := by decide +kernel

#print axioms solution
