-- Prove2me | Definitions.Def_HardyCapsetEvaluationData023rows00V420261021
-- name    : HardyCapsetEvaluationData023rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:04:16.673786+00:00
-- url     : https://prove2.me/theorems/50a98cf4-03ac-40ab-afc8-2aa9dd893de7
-- title:
--   HardyCapsetEvaluationData023rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er023_000 : Row := { vars := #[9, 129], coeff := #[1, 1], bound := 1, weight := 183091, edges := #[⟨0, 1, 151⟩], triples := #[] }
def er023_001 : Row := { vars := #[18, 320], coeff := #[1, 1], bound := 1, weight := 51174, edges := #[⟨0, 1, 242⟩], triples := #[] }
def er023_002 : Row := { vars := #[20, 336], coeff := #[1, 1], bound := 1, weight := 19613, edges := #[⟨0, 1, 235⟩], triples := #[] }
def er023_003 : Row := { vars := #[20, 350], coeff := #[1, 1], bound := 1, weight := 149603, edges := #[⟨0, 1, 218⟩], triples := #[] }
def er023_004 : Row := { vars := #[42, 144], coeff := #[1, 1], bound := 1, weight := 296830, edges := #[⟨0, 1, 109⟩], triples := #[] }
def er023_005 : Row := { vars := #[50, 275], coeff := #[1, 1], bound := 1, weight := 172495, edges := #[⟨0, 1, 491⟩], triples := #[] }
def er023_006 : Row := { vars := #[78, 402], coeff := #[1, 1], bound := 1, weight := 52123, edges := #[⟨0, 1, 234⟩], triples := #[] }
def er023_007 : Row := { vars := #[81, 356], coeff := #[1, 1], bound := 1, weight := 12929, edges := #[⟨0, 1, 309⟩], triples := #[] }
def er023_008 : Row := { vars := #[105, 262], coeff := #[1, 1], bound := 1, weight := 113845, edges := #[⟨0, 1, 414⟩], triples := #[] }
def er023_009 : Row := { vars := #[140, 303], coeff := #[1, 1], bound := 1, weight := 33285, edges := #[⟨0, 1, 468⟩], triples := #[] }
def er023_010 : Row := { vars := #[143, 205], coeff := #[1, 1], bound := 1, weight := 240487, edges := #[⟨0, 1, 405⟩], triples := #[] }
def er023_011 : Row := { vars := #[245, 349], coeff := #[1, 1], bound := 1, weight := 145950, edges := #[⟨0, 1, 169⟩], triples := #[] }
def er023_012 : Row := { vars := #[290, 375], coeff := #[1, 1], bound := 1, weight := 76529, edges := #[⟨0, 1, 1⟩], triples := #[] }
def er023_013 : Row := { vars := #[304, 338], coeff := #[1, 1], bound := 1, weight := 18837, edges := #[⟨0, 1, 109⟩], triples := #[] }
def er023_014 : Row := { vars := #[2, 299, 388], coeff := #[1, 1, 1], bound := 2, weight := 128410, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er023_015 : Row := { vars := #[3, 213, 316], coeff := #[1, 1, 1], bound := 2, weight := 179673, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er023_016 : Row := { vars := #[62, 301, 382], coeff := #[1, 1, 1], bound := 2, weight := 126327, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er023_017 : Row := { vars := #[144, 146, 158], coeff := #[1, 1, 1], bound := 2, weight := 4457, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er023_018 : Row := { vars := #[12, 256, 89, 370], coeff := #[1, 1, 1, 1], bound := 1, weight := 16394, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 189⟩, ⟨0, 3, 326⟩, ⟨1, 2, 442⟩, ⟨1, 3, 113⟩, ⟨2, 3, 282⟩], triples := #[] }
def er023_019 : Row := { vars := #[12, 256, 403], coeff := #[1, 1, 1], bound := 1, weight := 273481, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 255⟩, ⟨1, 2, 30⟩], triples := #[] }
def er023_020 : Row := { vars := #[15, 280, 383], coeff := #[1, 1, 1], bound := 1, weight := 253664, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 306⟩, ⟨1, 2, 33⟩], triples := #[] }
def er023_021 : Row := { vars := #[20, 354, 240, 123], coeff := #[1, 1, 1, 1], bound := 1, weight := 71967, edges := #[⟨0, 1, 208⟩, ⟨0, 2, 368⟩, ⟨0, 3, 150⟩, ⟨1, 2, 53⟩, ⟨1, 3, 337⟩, ⟨2, 3, 497⟩], triples := #[] }
def er023_022 : Row := { vars := #[24, 209, 351], coeff := #[1, 1, 1], bound := 1, weight := 383240, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 220⟩, ⟨1, 2, 14⟩], triples := #[] }
def er023_023 : Row := { vars := #[46, 394, 207], coeff := #[1, 1, 1], bound := 1, weight := 494878, edges := #[⟨0, 1, 254⟩, ⟨0, 2, 385⟩, ⟨1, 2, 79⟩], triples := #[] }
def er023_024 : Row := { vars := #[56, 149, 292, 406], coeff := #[1, 1, 1, 1], bound := 1, weight := 305168, edges := #[⟨0, 1, 114⟩, ⟨0, 2, 409⟩, ⟨0, 3, 249⟩, ⟨1, 2, 501⟩, ⟨1, 3, 341⟩, ⟨2, 3, 173⟩], triples := #[] }
def er023_025 : Row := { vars := #[56, 332, 249], coeff := #[1, 1, 1], bound := 1, weight := 645676, edges := #[⟨0, 1, 224⟩, ⟨0, 2, 469⟩, ⟨1, 2, 162⟩], triples := #[] }
def er023_026 : Row := { vars := #[61, 273, 384, 57], coeff := #[1, 1, 1, 1], bound := 1, weight := 117554, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 333⟩, ⟨0, 3, 42⟩, ⟨1, 2, 122⟩, ⟨1, 3, 490⟩, ⟨2, 3, 335⟩], triples := #[] }
def er023_027 : Row := { vars := #[61, 52, 57, 330, 270], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 183450, edges := #[⟨0, 1, 50⟩, ⟨0, 2, 42⟩, ⟨0, 3, 224⟩, ⟨0, 4, 493⟩, ⟨1, 2, 52⟩, ⟨1, 3, 230⟩, ⟨1, 4, 499⟩, ⟨2, 3, 229⟩, ⟨2, 4, 495⟩, ⟨3, 4, 174⟩], triples := #[] }
def er023_028 : Row := { vars := #[71, 398, 284, 188, 75], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 230747, edges := #[⟨0, 1, 212⟩, ⟨0, 2, 372⟩, ⟨0, 3, 30⟩, ⟨0, 4, 81⟩, ⟨1, 2, 149⟩, ⟨1, 3, 313⟩, ⟨1, 4, 221⟩, ⟨2, 3, 473⟩, ⟨2, 4, 381⟩, ⟨3, 4, 27⟩], triples := #[] }
def er023_029 : Row := { vars := #[74, 326, 229], coeff := #[1, 1, 1], bound := 1, weight := 383909, edges := #[⟨0, 1, 298⟩, ⟨0, 2, 490⟩, ⟨1, 2, 51⟩], triples := #[] }
def er023_030 : Row := { vars := #[75, 285, 334], coeff := #[1, 1, 1], bound := 1, weight := 577101, edges := #[⟨0, 1, 367⟩, ⟨0, 2, 303⟩, ⟨1, 2, 103⟩], triples := #[] }
def er023_031 : Row := { vars := #[77, 419, 228], coeff := #[1, 1, 1], bound := 1, weight := 96976, edges := #[⟨0, 1, 232⟩, ⟨0, 2, 490⟩, ⟨1, 2, 105⟩], triples := #[] }
def er023_032 : Row := { vars := #[78, 320, 236], coeff := #[1, 1, 1], bound := 1, weight := 14217, edges := #[⟨0, 1, 299⟩, ⟨0, 2, 469⟩, ⟨1, 2, 5⟩], triples := #[] }
def er023_033 : Row := { vars := #[81, 369, 242], coeff := #[1, 1, 1], bound := 1, weight := 399578, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 469⟩, ⟨1, 2, 137⟩], triples := #[] }
def er023_034 : Row := { vars := #[82, 337, 234], coeff := #[1, 1, 1], bound := 1, weight := 356174, edges := #[⟨0, 1, 298⟩, ⟨0, 2, 491⟩, ⟨1, 2, 69⟩], triples := #[] }
def er023_035 : Row := { vars := #[86, 281, 326], coeff := #[1, 1, 1], bound := 1, weight := 559280, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 307⟩, ⟨1, 2, 86⟩], triples := #[] }
def er023_036 : Row := { vars := #[86, 190, 212], coeff := #[1, 1, 1], bound := 1, weight := 265110, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 467⟩, ⟨1, 2, 420⟩], triples := #[] }
def er023_037 : Row := { vars := #[87, 332, 231], coeff := #[1, 1, 1], bound := 1, weight := 27633, edges := #[⟨0, 1, 298⟩, ⟨0, 2, 498⟩, ⟨1, 2, 51⟩], triples := #[] }
def er023_038 : Row := { vars := #[98, 72, 91], coeff := #[1, 1, 1], bound := 1, weight := 503925, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 98⟩, ⟨1, 2, 88⟩], triples := #[] }
def er023_039 : Row := { vars := #[140, 220, 363], coeff := #[1, 1, 1], bound := 1, weight := 844019, edges := #[⟨0, 1, 409⟩, ⟨0, 2, 207⟩, ⟨1, 2, 163⟩], triples := #[] }
def er023_040 : Row := { vars := #[143, 225, 119], coeff := #[1, 1, 1], bound := 1, weight := 156769, edges := #[⟨0, 1, 410⟩, ⟨0, 2, 0⟩, ⟨1, 2, 473⟩], triples := #[] }
def er023_041 : Row := { vars := #[145, 356, 255], coeff := #[1, 1, 1], bound := 1, weight := 354874, edges := #[⟨0, 1, 254⟩, ⟨0, 2, 400⟩, ⟨1, 2, 137⟩], triples := #[] }
def er023_042 : Row := { vars := #[146, 29, 244], coeff := #[1, 1, 1], bound := 1, weight := 52874, edges := #[⟨0, 1, 122⟩, ⟨0, 2, 379⟩, ⟨1, 2, 499⟩], triples := #[] }
def er023_043 : Row := { vars := #[147, 207, 358], coeff := #[1, 1, 1], bound := 1, weight := 186433, edges := #[⟨0, 1, 412⟩, ⟨0, 2, 218⟩, ⟨1, 2, 139⟩], triples := #[] }
def er023_044 : Row := { vars := #[151, 29, 359], coeff := #[1, 1, 1], bound := 1, weight := 204612, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 223⟩, ⟨1, 2, 335⟩], triples := #[] }
def er023_045 : Row := { vars := #[201, 403, 122], coeff := #[1, 1, 1], bound := 1, weight := 127295, edges := #[⟨0, 1, 121⟩, ⟨0, 2, 486⟩, ⟨1, 2, 212⟩], triples := #[] }
def er023_046 : Row := { vars := #[201, 168, 218], coeff := #[1, 1, 1], bound := 1, weight := 26046, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 211⟩, ⟨1, 2, 445⟩], triples := #[] }
def er023_047 : Row := { vars := #[204, 217, 123], coeff := #[1, 1, 1], bound := 1, weight := 23322, edges := #[⟨0, 1, 210⟩, ⟨0, 2, 482⟩, ⟨1, 2, 471⟩], triples := #[] }
def er023_048 : Row := { vars := #[216, 205, 126], coeff := #[1, 1, 1], bound := 1, weight := 335969, edges := #[⟨0, 1, 222⟩, ⟨0, 2, 468⟩, ⟨1, 2, 479⟩], triples := #[] }
def er023_049 : Row := { vars := #[227, 168, 370], coeff := #[1, 1, 1], bound := 1, weight := 66403, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 177⟩, ⟨1, 2, 231⟩], triples := #[] }
def er023_050 : Row := { vars := #[227, 224, 241], coeff := #[1, 1, 1], bound := 1, weight := 269536, edges := #[⟨0, 1, 239⟩, ⟨0, 2, 210⟩, ⟨1, 2, 231⟩], triples := #[] }
def er023_051 : Row := { vars := #[235, 395, 105], coeff := #[1, 1, 1], bound := 1, weight := 196867, edges := #[⟨0, 1, 109⟩, ⟨0, 2, 467⟩, ⟨1, 2, 241⟩], triples := #[] }
def er023_052 : Row := { vars := #[238, 22, 27, 126], coeff := #[1, 1, 1, 1], bound := 1, weight := 140287, edges := #[⟨0, 1, 368⟩, ⟨0, 2, 364⟩, ⟨0, 3, 491⟩, ⟨1, 2, 17⟩, ⟨1, 3, 145⟩, ⟨2, 3, 137⟩], triples := #[] }
def er023_053 : Row := { vars := #[251, 320, 26], coeff := #[1, 1, 1], bound := 1, weight := 131239, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 482⟩, ⟨1, 2, 241⟩], triples := #[] }
def er023_054 : Row := { vars := #[258, 252, 257], coeff := #[1, 1, 1], bound := 1, weight := 46023, edges := #[⟨0, 1, 262⟩, ⟨0, 2, 268⟩, ⟨1, 2, 259⟩], triples := #[] }
def er023_055 : Row := { vars := #[260, 185, 191], coeff := #[1, 1, 1], bound := 1, weight := 181355, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 381⟩, ⟨1, 2, 185⟩], triples := #[] }
def er023_056 : Row := { vars := #[264, 320, 191], coeff := #[1, 1, 1], bound := 1, weight := 210350, edges := #[⟨0, 1, 187⟩, ⟨0, 2, 377⟩, ⟨1, 2, 265⟩], triples := #[] }
def er023_057 : Row := { vars := #[264, 212, 311], coeff := #[1, 1, 1], bound := 1, weight := 214584, edges := #[⟨0, 1, 342⟩, ⟨0, 2, 223⟩, ⟨1, 2, 265⟩], triples := #[] }
def er023_058 : Row := { vars := #[272, 302, 307], coeff := #[1, 1, 1], bound := 1, weight := 317965, edges := #[⟨0, 1, 239⟩, ⟨0, 2, 242⟩, ⟨1, 2, 337⟩], triples := #[] }
def er023_059 : Row := { vars := #[276, 11, 399], coeff := #[1, 1, 1], bound := 1, weight := 17840, edges := #[⟨0, 1, 463⟩, ⟨0, 2, 27⟩, ⟨1, 2, 285⟩], triples := #[] }
def er023_060 : Row := { vars := #[276, 303, 311], coeff := #[1, 1, 1], bound := 1, weight := 603960, edges := #[⟨0, 1, 240⟩, ⟨0, 2, 243⟩, ⟨1, 2, 341⟩], triples := #[] }
def er023_061 : Row := { vars := #[279, 322, 343], coeff := #[1, 1, 1], bound := 1, weight := 486094, edges := #[⟨0, 1, 80⟩, ⟨0, 2, 120⟩, ⟨1, 2, 397⟩], triples := #[] }
def er023_062 : Row := { vars := #[282, 398, 210], coeff := #[1, 1, 1], bound := 1, weight := 159078, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 252⟩, ⟨1, 2, 103⟩], triples := #[] }
def er023_063 : Row := { vars := #[282, 190, 88, 83], coeff := #[1, 1, 1, 1], bound := 1, weight := 21104, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 367⟩, ⟨0, 3, 371⟩, ⟨1, 2, 7⟩, ⟨1, 3, 15⟩, ⟨2, 3, 88⟩], triples := #[] }
end HardyCapset20261020.Cert


