-- Prove2me | solution 1 for Apery.PotentialCertificate.TableBlock576_639.checked
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:14:17.298986+00:00
-- url     : https://prove2.me/submissions/16c3a711-59c2-40e1-8637-4d4161b71996

import Definitions.Def_Zeta5_PotentialTableBlock576_639Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem solution : Apery.PotentialCertificate.TableBlock576_639.certificate.Valid := by decide +kernel

#print axioms solution
