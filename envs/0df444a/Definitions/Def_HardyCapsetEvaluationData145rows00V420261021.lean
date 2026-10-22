-- Prove2me | Definitions.Def_HardyCapsetEvaluationData145rows00V420261021
-- name    : HardyCapsetEvaluationData145rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:53:47.064623+00:00
-- url     : https://prove2.me/theorems/d54fee5d-f7cf-4315-a6ae-fda2435ac460
-- title:
--   HardyCapsetEvaluationData145rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er145_000 : Row := { vars := #[4, 199], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 432⟩], triples := #[] }
def er145_001 : Row := { vars := #[6, 97], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 157⟩], triples := #[] }
def er145_002 : Row := { vars := #[14, 115], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 112⟩], triples := #[] }
def er145_003 : Row := { vars := #[14, 120], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 88⟩], triples := #[] }
def er145_004 : Row := { vars := #[17, 186], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 458⟩], triples := #[] }
def er145_005 : Row := { vars := #[29, 176], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 464⟩], triples := #[] }
def er145_006 : Row := { vars := #[31, 56], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 187⟩], triples := #[] }
def er145_007 : Row := { vars := #[32, 43], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 67⟩], triples := #[] }
def er145_008 : Row := { vars := #[35, 52], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 59⟩], triples := #[] }
def er145_009 : Row := { vars := #[41, 76], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 170⟩], triples := #[] }
def er145_010 : Row := { vars := #[46, 54], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 50⟩], triples := #[] }
def er145_011 : Row := { vars := #[52, 110], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 119⟩], triples := #[] }
def er145_012 : Row := { vars := #[55, 67], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 104⟩], triples := #[] }
def er145_013 : Row := { vars := #[88, 116], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 28⟩], triples := #[] }
def er145_014 : Row := { vars := #[89, 236], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 320⟩], triples := #[] }
def er145_015 : Row := { vars := #[91, 101], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 8⟩], triples := #[] }
def er145_016 : Row := { vars := #[91, 111], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 18⟩], triples := #[] }
def er145_017 : Row := { vars := #[94, 197], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 376⟩], triples := #[] }
def er145_018 : Row := { vars := #[99, 160], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 367⟩], triples := #[] }
def er145_019 : Row := { vars := #[101, 220], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 477⟩], triples := #[] }
def er145_020 : Row := { vars := #[105, 111], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 138⟩], triples := #[] }
def er145_021 : Row := { vars := #[107, 112], coeff := #[1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 146⟩], triples := #[] }
def er145_022 : Row := { vars := #[108, 313], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 308⟩], triples := #[] }
def er145_023 : Row := { vars := #[114, 200], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 477⟩], triples := #[] }
def er145_024 : Row := { vars := #[125, 188], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 317⟩], triples := #[] }
def er145_025 : Row := { vars := #[126, 135], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 220⟩], triples := #[] }
def er145_026 : Row := { vars := #[130, 139], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 196⟩], triples := #[] }
def er145_027 : Row := { vars := #[130, 194], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 289⟩], triples := #[] }
def er145_028 : Row := { vars := #[132, 136], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 207⟩], triples := #[] }
def er145_029 : Row := { vars := #[145, 262], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 169⟩], triples := #[] }
def er145_030 : Row := { vars := #[148, 175], coeff := #[1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 307⟩], triples := #[] }
def er145_031 : Row := { vars := #[155, 295], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 62⟩], triples := #[] }
def er145_032 : Row := { vars := #[157, 293], coeff := #[1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 62⟩], triples := #[] }
def er145_033 : Row := { vars := #[229, 231], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 368⟩], triples := #[] }
def er145_034 : Row := { vars := #[245, 262], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 486⟩], triples := #[] }
def er145_035 : Row := { vars := #[252, 267], coeff := #[1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 447⟩], triples := #[] }
def er145_036 : Row := { vars := #[256, 298], coeff := #[1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 403⟩], triples := #[] }
def er145_037 : Row := { vars := #[257, 298], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 402⟩], triples := #[] }
def er145_038 : Row := { vars := #[289, 294], coeff := #[1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 481⟩], triples := #[] }
def er145_039 : Row := { vars := #[98, 189, 288], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er145_040 : Row := { vars := #[121, 212, 311], coeff := #[1, 1, 1], bound := 2, weight := 4, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er145_041 : Row := { vars := #[121, 215, 308], coeff := #[1, 1, 1], bound := 2, weight := 4, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er145_042 : Row := { vars := #[1, 73, 27], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 65⟩, ⟨1, 2, 191⟩], triples := #[] }
def er145_043 : Row := { vars := #[2, 57, 68], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 147⟩, ⟨1, 2, 104⟩], triples := #[] }
def er145_044 : Row := { vars := #[3, 141, 277], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 399⟩, ⟨0, 2, 299⟩, ⟨1, 2, 175⟩], triples := #[] }
def er145_045 : Row := { vars := #[3, 181, 237], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 239⟩, ⟨1, 2, 175⟩], triples := #[] }
def er145_046 : Row := { vars := #[5, 167, 118], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 79⟩, ⟨1, 2, 353⟩], triples := #[] }
def er145_047 : Row := { vars := #[8, 180, 232], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 243⟩, ⟨1, 2, 177⟩], triples := #[] }
def er145_048 : Row := { vars := #[16, 167, 249], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 484⟩, ⟨0, 2, 212⟩, ⟨1, 2, 132⟩], triples := #[] }
def er145_049 : Row := { vars := #[18, 269, 118], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 309⟩, ⟨0, 2, 104⟩, ⟨1, 2, 201⟩], triples := #[] }
def er145_050 : Row := { vars := #[18, 173, 24], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 15⟩, ⟨1, 2, 484⟩], triples := #[] }
def er145_051 : Row := { vars := #[20, 71, 190], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 458⟩, ⟨1, 2, 428⟩], triples := #[] }
def er145_052 : Row := { vars := #[20, 72, 123], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 80⟩, ⟨1, 2, 26⟩], triples := #[] }
def er145_053 : Row := { vars := #[21, 171, 119], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 107⟩, ⟨1, 2, 361⟩], triples := #[] }
def er145_054 : Row := { vars := #[24, 130, 269], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 397⟩, ⟨0, 2, 324⟩, ⟨1, 2, 181⟩], triples := #[] }
def er145_055 : Row := { vars := #[25, 71, 279], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 298⟩, ⟨1, 2, 254⟩], triples := #[] }
def er145_056 : Row := { vars := #[32, 80, 197], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 132⟩, ⟨0, 2, 404⟩, ⟨1, 2, 384⟩], triples := #[] }
def er145_057 : Row := { vars := #[36, 82, 292], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 140⟩, ⟨0, 2, 244⟩, ⟨1, 2, 224⟩], triples := #[] }
def er145_058 : Row := { vars := #[37, 276, 60], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 331⟩, ⟨0, 2, 170⟩, ⟨1, 2, 254⟩], triples := #[] }
def er145_059 : Row := { vars := #[38, 48, 51], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 70⟩, ⟨0, 2, 56⟩, ⟨1, 2, 41⟩], triples := #[] }
def er145_060 : Row := { vars := #[39, 84, 165], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 163⟩, ⟨0, 2, 458⟩, ⟨1, 2, 433⟩], triples := #[] }
def er145_061 : Row := { vars := #[42, 66, 202], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 404⟩, ⟨1, 2, 394⟩], triples := #[] }
def er145_062 : Row := { vars := #[45, 109, 161], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 468⟩, ⟨1, 2, 376⟩], triples := #[] }
def er145_063 : Row := { vars := #[45, 109, 257], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 308⟩, ⟨1, 2, 216⟩], triples := #[] }
end HardyCapset20261020.Cert


