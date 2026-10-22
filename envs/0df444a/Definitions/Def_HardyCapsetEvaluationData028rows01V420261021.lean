-- Prove2me | Definitions.Def_HardyCapsetEvaluationData028rows01V420261021
-- name    : HardyCapsetEvaluationData028rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:22:24.960925+00:00
-- url     : https://prove2.me/theorems/b72cdee5-c80a-4c3b-b459-ce2465ee9338
-- title:
--   HardyCapsetEvaluationData028rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er028_064 : Row := { vars := #[39, 523, 372], coeff := #[1, 1, 1], bound := 1, weight := 470341, edges := #[⟨0, 1, 246⟩, ⟨0, 2, 438⟩, ⟨1, 2, 139⟩], triples := #[] }
def er028_065 : Row := { vars := #[39, 307, 328], coeff := #[1, 1, 1], bound := 1, weight := 38650, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 407⟩, ⟨1, 2, 207⟩], triples := #[] }
def er028_066 : Row := { vars := #[39, 474, 485, 221], coeff := #[1, 1, 1, 1], bound := 1, weight := 491010, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 343⟩, ⟨0, 3, 365⟩, ⟨1, 2, 450⟩, ⟨1, 3, 157⟩, ⟨2, 3, 147⟩], triples := #[] }
def er028_067 : Row := { vars := #[41, 44, 418, 226], coeff := #[1, 1, 1, 1], bound := 1, weight := 584420, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 237⟩, ⟨0, 3, 397⟩, ⟨1, 2, 236⟩, ⟨1, 3, 396⟩, ⟨2, 3, 62⟩], triples := #[] }
def er028_068 : Row := { vars := #[46, 275, 404], coeff := #[1, 1, 1], bound := 1, weight := 15679, edges := #[⟨0, 1, 461⟩, ⟨0, 2, 438⟩, ⟨1, 2, 223⟩], triples := #[] }
def er028_069 : Row := { vars := #[46, 303, 464], coeff := #[1, 1, 1], bound := 1, weight := 806598, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 300⟩, ⟨1, 2, 87⟩], triples := #[] }
def er028_070 : Row := { vars := #[46, 48, 185, 187], coeff := #[1, 1, 1, 1], bound := 1, weight := 42365, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 82⟩, ⟨0, 3, 85⟩, ⟨1, 2, 74⟩, ⟨1, 3, 77⟩, ⟨2, 3, 177⟩], triples := #[] }
def er028_071 : Row := { vars := #[47, 392, 554], coeff := #[1, 1, 1], bound := 1, weight := 189405, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 246⟩, ⟨1, 2, 147⟩], triples := #[] }
def er028_072 : Row := { vars := #[47, 49, 107, 109], coeff := #[1, 1, 1, 1], bound := 1, weight := 382846, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 142⟩, ⟨0, 3, 145⟩, ⟨1, 2, 134⟩, ⟨1, 3, 137⟩, ⟨2, 3, 117⟩], triples := #[] }
def er028_073 : Row := { vars := #[47, 505, 508, 219], coeff := #[1, 1, 1, 1], bound := 1, weight := 427750, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 333⟩, ⟨0, 3, 369⟩, ⟨1, 2, 454⟩, ⟨1, 3, 136⟩, ⟨2, 3, 139⟩], triples := #[] }
def er028_074 : Row := { vars := #[48, 387, 370, 410], coeff := #[1, 1, 1, 1], bound := 1, weight := 387570, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 449⟩, ⟨0, 3, 204⟩, ⟨1, 2, 344⟩, ⟨1, 3, 97⟩, ⟨2, 3, 107⟩], triples := #[] }
def er028_075 : Row := { vars := #[48, 269, 51], coeff := #[1, 1, 1], bound := 1, weight := 570067, edges := #[⟨0, 1, 461⟩, ⟨0, 2, 40⟩, ⟨1, 2, 467⟩], triples := #[] }
def er028_076 : Row := { vars := #[49, 499, 502, 219], coeff := #[1, 1, 1, 1], bound := 1, weight := 572251, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 333⟩, ⟨0, 3, 365⟩, ⟨1, 2, 450⟩, ⟨1, 3, 144⟩, ⟨2, 3, 147⟩], triples := #[] }
def er028_077 : Row := { vars := #[51, 238, 414], coeff := #[1, 1, 1], bound := 1, weight := 187840, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 238⟩, ⟨1, 2, 145⟩], triples := #[] }
def er028_078 : Row := { vars := #[52, 285, 173, 573], coeff := #[1, 1, 1, 1], bound := 1, weight := 586225, edges := #[⟨0, 1, 498⟩, ⟨0, 2, 97⟩, ⟨0, 3, 278⟩, ⟨1, 2, 359⟩, ⟨1, 3, 67⟩, ⟨2, 3, 307⟩], triples := #[] }
def er028_079 : Row := { vars := #[52, 291, 568, 95], coeff := #[1, 1, 1, 1], bound := 1, weight := 17866, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 284⟩, ⟨0, 3, 157⟩, ⟨1, 2, 66⟩, ⟨1, 3, 413⟩, ⟨2, 3, 198⟩], triples := #[] }
def er028_080 : Row := { vars := #[53, 417, 356], coeff := #[1, 1, 1], bound := 1, weight := 2685, edges := #[⟨0, 1, 237⟩, ⟨0, 2, 413⟩, ⟨1, 2, 82⟩], triples := #[] }
def er028_081 : Row := { vars := #[56, 390, 393, 412], coeff := #[1, 1, 1, 1], bound := 1, weight := 365611, edges := #[⟨0, 1, 439⟩, ⟨0, 2, 438⟩, ⟨0, 3, 220⟩, ⟨1, 2, 342⟩, ⟨1, 3, 79⟩, ⟨2, 3, 76⟩], triples := #[] }
def er028_082 : Row := { vars := #[56, 58, 171, 187], coeff := #[1, 1, 1, 1], bound := 1, weight := 247482, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 95⟩, ⟨0, 3, 105⟩, ⟨1, 2, 92⟩, ⟨1, 3, 102⟩, ⟨2, 3, 175⟩], triples := #[] }
def er028_083 : Row := { vars := #[56, 58, 92, 108], coeff := #[1, 1, 1, 1], bound := 1, weight := 83350, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 157⟩, ⟨0, 3, 167⟩, ⟨1, 2, 154⟩, ⟨1, 3, 164⟩, ⟨2, 3, 114⟩], triples := #[] }
def er028_084 : Row := { vars := #[57, 543, 378], coeff := #[1, 1, 1], bound := 1, weight := 321479, edges := #[⟨0, 1, 246⟩, ⟨0, 2, 440⟩, ⟨1, 2, 167⟩], triples := #[] }
def er028_085 : Row := { vars := #[57, 491, 494, 221], coeff := #[1, 1, 1, 1], bound := 1, weight := 508991, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 332⟩, ⟨0, 3, 381⟩, ⟨1, 2, 448⟩, ⟨1, 3, 139⟩, ⟨2, 3, 136⟩], triples := #[] }
def er028_086 : Row := { vars := #[58, 384, 387, 412], coeff := #[1, 1, 1, 1], bound := 1, weight := 138900, edges := #[⟨0, 1, 439⟩, ⟨0, 2, 438⟩, ⟨0, 3, 216⟩, ⟨1, 2, 338⟩, ⟨1, 3, 87⟩, ⟨2, 3, 84⟩], triples := #[] }
def er028_087 : Row := { vars := #[58, 311, 444], coeff := #[1, 1, 1], bound := 1, weight := 530271, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 301⟩, ⟨1, 2, 76⟩], triples := #[] }
def er028_088 : Row := { vars := #[59, 386, 523], coeff := #[1, 1, 1], bound := 1, weight := 202951, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 248⟩, ⟨1, 2, 164⟩], triples := #[] }
def er028_089 : Row := { vars := #[59, 293, 345], coeff := #[1, 1, 1], bound := 1, weight := 541384, edges := #[⟨0, 1, 493⟩, ⟨0, 2, 406⟩, ⟨1, 2, 207⟩], triples := #[] }
def er028_090 : Row := { vars := #[59, 296, 342], coeff := #[1, 1, 1], bound := 1, weight := 93515, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 407⟩, ⟨1, 2, 207⟩], triples := #[] }
def er028_091 : Row := { vars := #[61, 74, 181, 183], coeff := #[1, 1, 1, 1], bound := 1, weight := 340511, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 69⟩, ⟨0, 3, 66⟩, ⟨1, 2, 59⟩, ⟨1, 3, 56⟩, ⟨2, 3, 175⟩], triples := #[] }
def er028_092 : Row := { vars := #[61, 81, 410, 216], coeff := #[1, 1, 1, 1], bound := 1, weight := 154547, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 343⟩, ⟨0, 3, 493⟩, ⟨1, 2, 332⟩, ⟨1, 3, 494⟩, ⟨2, 3, 26⟩], triples := #[] }
def er028_093 : Row := { vars := #[61, 81, 421, 231], coeff := #[1, 1, 1, 1], bound := 1, weight := 486637, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 247⟩, ⟨0, 3, 411⟩, ⟨1, 2, 248⟩, ⟨1, 3, 406⟩, ⟨2, 3, 99⟩], triples := #[] }
def er028_094 : Row := { vars := #[62, 360, 66], coeff := #[1, 1, 1], bound := 1, weight := 220672, edges := #[⟨0, 1, 399⟩, ⟨0, 2, 85⟩, ⟨1, 2, 398⟩], triples := #[] }
def er028_095 : Row := { vars := #[62, 75, 416, 224], coeff := #[1, 1, 1, 1], bound := 1, weight := 492286, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 321⟩, ⟨0, 3, 481⟩, ⟨1, 2, 312⟩, ⟨1, 3, 472⟩, ⟨2, 3, 54⟩], triples := #[] }
def er028_096 : Row := { vars := #[62, 82, 416, 222], coeff := #[1, 1, 1, 1], bound := 1, weight := 217647, edges := #[⟨0, 1, 91⟩, ⟨0, 2, 321⟩, ⟨0, 3, 471⟩, ⟨1, 2, 310⟩, ⟨1, 3, 472⟩, ⟨2, 3, 62⟩], triples := #[] }
def er028_097 : Row := { vars := #[63, 256, 511, 87], coeff := #[1, 1, 1, 1], bound := 1, weight := 379908, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 192⟩, ⟨0, 3, 96⟩, ⟨1, 2, 66⟩, ⟨1, 3, 439⟩, ⟨2, 3, 211⟩], triples := #[] }
def er028_098 : Row := { vars := #[63, 515, 89, 267], coeff := #[1, 1, 1, 1], bound := 1, weight := 12571, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 93⟩, ⟨0, 3, 448⟩, ⟨1, 2, 219⟩, ⟨1, 3, 69⟩, ⟨2, 3, 449⟩], triples := #[] }
def er028_099 : Row := { vars := #[63, 515, 273, 87], coeff := #[1, 1, 1, 1], bound := 1, weight := 133847, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 444⟩, ⟨0, 3, 96⟩, ⟨1, 2, 66⟩, ⟨1, 3, 223⟩, ⟨2, 3, 449⟩], triples := #[] }
def er028_100 : Row := { vars := #[63, 89, 250, 511], coeff := #[1, 1, 1, 1], bound := 1, weight := 473676, edges := #[⟨0, 1, 93⟩, ⟨0, 2, 454⟩, ⟨0, 3, 192⟩, ⟨1, 2, 439⟩, ⟨1, 3, 207⟩, ⟨2, 3, 69⟩], triples := #[] }
def er028_101 : Row := { vars := #[64, 71, 173, 191], coeff := #[1, 1, 1, 1], bound := 1, weight := 273450, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 46⟩, ⟨0, 3, 56⟩, ⟨1, 2, 69⟩, ⟨1, 3, 41⟩, ⟨2, 3, 175⟩], triples := #[] }
def er028_102 : Row := { vars := #[64, 71, 175, 189], coeff := #[1, 1, 1, 1], bound := 1, weight := 52472, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 38⟩, ⟨0, 3, 59⟩, ⟨1, 2, 66⟩, ⟨1, 3, 49⟩, ⟨2, 3, 175⟩], triples := #[] }
def er028_103 : Row := { vars := #[64, 71, 198, 212], coeff := #[1, 1, 1, 1], bound := 1, weight := 92208, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 4⟩, ⟨0, 3, 25⟩, ⟨1, 2, 32⟩, ⟨1, 3, 15⟩, ⟨2, 3, 186⟩], triples := #[] }
def er028_104 : Row := { vars := #[64, 71, 366, 586], coeff := #[1, 1, 1, 1], bound := 1, weight := 498858, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 386⟩, ⟨0, 3, 228⟩, ⟨1, 2, 391⟩, ⟨1, 3, 227⟩, ⟨2, 3, 186⟩], triples := #[] }
def er028_105 : Row := { vars := #[64, 84, 220, 412], coeff := #[1, 1, 1, 1], bound := 1, weight := 83014, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 494⟩, ⟨0, 3, 334⟩, ⟨1, 2, 503⟩, ⟨1, 3, 343⟩, ⟨2, 3, 26⟩], triples := #[] }
def er028_106 : Row := { vars := #[65, 72, 414, 226], coeff := #[1, 1, 1, 1], bound := 1, weight := 247393, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 310⟩, ⟨0, 3, 472⟩, ⟨1, 2, 321⟩, ⟨1, 3, 471⟩, ⟨2, 3, 54⟩], triples := #[] }
def er028_107 : Row := { vars := #[65, 340, 68], coeff := #[1, 1, 1], bound := 1, weight := 752608, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 74⟩, ⟨1, 2, 401⟩], triples := #[] }
def er028_108 : Row := { vars := #[66, 527, 72], coeff := #[1, 1, 1], bound := 1, weight := 244894, edges := #[⟨0, 1, 236⟩, ⟨0, 2, 105⟩, ⟨1, 2, 242⟩], triples := #[] }
def er028_109 : Row := { vars := #[66, 527, 247], coeff := #[1, 1, 1], bound := 1, weight := 534436, edges := #[⟨0, 1, 236⟩, ⟨0, 2, 438⟩, ⟨1, 2, 13⟩], triples := #[] }
def er028_110 : Row := { vars := #[67, 437, 323, 448], coeff := #[1, 1, 1, 1], bound := 1, weight := 531135, edges := #[⟨0, 1, 278⟩, ⟨0, 2, 371⟩, ⟨0, 3, 289⟩, ⟨1, 2, 56⟩, ⟨1, 3, 432⟩, ⟨2, 3, 41⟩], triples := #[] }
def er028_111 : Row := { vars := #[67, 79, 209, 193], coeff := #[1, 1, 1, 1], bound := 1, weight := 468866, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 23⟩, ⟨0, 3, 13⟩, ⟨1, 2, 2⟩, ⟨1, 3, 30⟩, ⟨2, 3, 187⟩], triples := #[] }
def er028_112 : Row := { vars := #[68, 471, 320, 80], coeff := #[1, 1, 1, 1], bound := 1, weight := 247393, edges := #[⟨0, 1, 257⟩, ⟨0, 2, 378⟩, ⟨0, 3, 94⟩, ⟨1, 2, 33⟩, ⟨1, 3, 266⟩, ⟨2, 3, 354⟩], triples := #[] }
def er028_113 : Row := { vars := #[69, 397, 498], coeff := #[1, 1, 1], bound := 1, weight := 555479, edges := #[⟨0, 1, 388⟩, ⟨0, 2, 258⟩, ⟨1, 2, 66⟩], triples := #[] }
def er028_114 : Row := { vars := #[69, 239, 383], coeff := #[1, 1, 1], bound := 1, weight := 444522, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 391⟩, ⟨1, 2, 216⟩], triples := #[] }
def er028_115 : Row := { vars := #[71, 74, 394, 586], coeff := #[1, 1, 1, 1], bound := 1, weight := 64707, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 387⟩, ⟨0, 3, 227⟩, ⟨1, 2, 386⟩, ⟨1, 3, 226⟩, ⟨2, 3, 188⟩], triples := #[] }
def er028_116 : Row := { vars := #[76, 524, 275], coeff := #[1, 1, 1], bound := 1, weight := 427750, edges := #[⟨0, 1, 241⟩, ⟨0, 2, 439⟩, ⟨1, 2, 23⟩], triples := #[] }
def er028_117 : Row := { vars := #[76, 505, 320, 508], coeff := #[1, 1, 1, 1], bound := 1, weight := 572251, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 370⟩, ⟨0, 3, 257⟩, ⟨1, 2, 2⟩, ⟨1, 3, 454⟩, ⟨2, 3, 5⟩], triples := #[] }
def er028_118 : Row := { vars := #[77, 270, 511, 242], coeff := #[1, 1, 1, 1], bound := 1, weight := 146418, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 223⟩, ⟨0, 3, 449⟩, ⟨1, 2, 56⟩, ⟨1, 3, 266⟩, ⟨2, 3, 41⟩], triples := #[] }
def er028_119 : Row := { vars := #[77, 270, 406], coeff := #[1, 1, 1], bound := 1, weight := 206803, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 387⟩, ⟨1, 2, 220⟩], triples := #[] }
def er028_120 : Row := { vars := #[77, 434, 321, 451], coeff := #[1, 1, 1, 1], bound := 1, weight := 547904, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 371⟩, ⟨0, 3, 280⟩, ⟨1, 2, 66⟩, ⟨1, 3, 432⟩, ⟨2, 3, 56⟩], triples := #[] }
def er028_121 : Row := { vars := #[77, 79, 211, 209], coeff := #[1, 1, 1, 1], bound := 1, weight := 98877, edges := #[⟨0, 1, 91⟩, ⟨0, 2, 13⟩, ⟨0, 3, 10⟩, ⟨1, 2, 5⟩, ⟨1, 3, 2⟩, ⟨2, 3, 189⟩], triples := #[] }
def er028_122 : Row := { vars := #[78, 279, 512, 296], coeff := #[1, 1, 1, 1], bound := 1, weight := 640072, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 206⟩, ⟨0, 3, 418⟩, ⟨1, 2, 33⟩, ⟨1, 3, 290⟩, ⟨2, 3, 23⟩], triples := #[] }
def er028_123 : Row := { vars := #[78, 549, 238], coeff := #[1, 1, 1], bound := 1, weight := 148073, edges := #[⟨0, 1, 237⟩, ⟨0, 2, 449⟩, ⟨1, 2, 20⟩], triples := #[] }
def er028_124 : Row := { vars := #[78, 471, 318, 80], coeff := #[1, 1, 1, 1], bound := 1, weight := 123276, edges := #[⟨0, 1, 267⟩, ⟨0, 2, 378⟩, ⟨0, 3, 76⟩, ⟨1, 2, 13⟩, ⟨1, 3, 266⟩, ⟨2, 3, 362⟩], triples := #[] }
def er028_125 : Row := { vars := #[78, 354, 85], coeff := #[1, 1, 1], bound := 1, weight := 88581, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 77⟩, ⟨1, 2, 403⟩], triples := #[] }
def er028_126 : Row := { vars := #[79, 264, 513, 267], coeff := #[1, 1, 1, 1], bound := 1, weight := 230352, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 207⟩, ⟨0, 3, 439⟩, ⟨1, 2, 46⟩, ⟨1, 3, 268⟩, ⟨2, 3, 49⟩], triples := #[] }
def er028_127 : Row := { vars := #[79, 397, 84], coeff := #[1, 1, 1], bound := 1, weight := 201907, edges := #[⟨0, 1, 386⟩, ⟨0, 2, 77⟩, ⟨1, 2, 393⟩], triples := #[] }
end HardyCapset20261020.Cert


