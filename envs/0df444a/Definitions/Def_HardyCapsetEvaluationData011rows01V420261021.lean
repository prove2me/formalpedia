-- Prove2me | Definitions.Def_HardyCapsetEvaluationData011rows01V420261021
-- name    : HardyCapsetEvaluationData011rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:44:14.934152+00:00
-- url     : https://prove2.me/theorems/13c4a38d-14f3-40cd-9ec4-d6f5fe7db8da
-- title:
--   HardyCapsetEvaluationData011rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er011_064 : Row := { vars := #[250, 40, 34, 39], coeff := #[1, 1, 1, 1], bound := 1, weight := 65974, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 472⟩, ⟨0, 3, 470⟩, ⟨1, 2, 15⟩, ⟨1, 3, 35⟩, ⟨2, 3, 9⟩], triples := #[] }
def er011_065 : Row := { vars := #[250, 302, 220], coeff := #[1, 1, 1], bound := 1, weight := 112486, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 333⟩, ⟨1, 2, 263⟩], triples := #[] }
def er011_066 : Row := { vars := #[250, 327, 379], coeff := #[1, 1, 1], bound := 1, weight := 205391, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 99⟩, ⟨1, 2, 488⟩], triples := #[] }
def er011_067 : Row := { vars := #[251, 174, 342], coeff := #[1, 1, 1], bound := 1, weight := 28509, edges := #[⟨0, 1, 388⟩, ⟨0, 2, 174⟩, ⟨1, 2, 264⟩], triples := #[] }
def er011_068 : Row := { vars := #[252, 129, 131, 41], coeff := #[1, 1, 1, 1], bound := 1, weight := 143115, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 406⟩, ⟨0, 3, 469⟩, ⟨1, 2, 123⟩, ⟨1, 3, 145⟩, ⟨2, 3, 165⟩], triples := #[] }
def er011_069 : Row := { vars := #[258, 301, 210], coeff := #[1, 1, 1], bound := 1, weight := 371517, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 332⟩, ⟨1, 2, 275⟩], triples := #[] }
def er011_070 : Row := { vars := #[258, 193, 333], coeff := #[1, 1, 1], bound := 1, weight := 185374, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 188⟩, ⟨1, 2, 275⟩], triples := #[] }
def er011_071 : Row := { vars := #[267, 315, 423], coeff := #[1, 1, 1], bound := 1, weight := 274750, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 54⟩, ⟨1, 2, 434⟩], triples := #[] }
def er011_072 : Row := { vars := #[272, 153, 337], coeff := #[1, 1, 1], bound := 1, weight := 24192, edges := #[⟨0, 1, 384⟩, ⟨0, 2, 149⟩, ⟨1, 2, 296⟩], triples := #[] }
def er011_073 : Row := { vars := #[272, 110, 68, 63], coeff := #[1, 1, 1, 1], bound := 1, weight := 1723, edges := #[⟨0, 1, 405⟩, ⟨0, 2, 503⟩, ⟨0, 3, 493⟩, ⟨1, 2, 142⟩, ⟨1, 3, 155⟩, ⟨2, 3, 45⟩], triples := #[] }
def er011_074 : Row := { vars := #[273, 175, 319], coeff := #[1, 1, 1], bound := 1, weight := 427382, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 175⟩, ⟨1, 2, 297⟩], triples := #[] }
def er011_075 : Row := { vars := #[281, 335, 98], coeff := #[1, 1, 1], bound := 1, weight := 178302, edges := #[⟨0, 1, 100⟩, ⟨0, 2, 374⟩, ⟨1, 2, 307⟩], triples := #[] }
def er011_076 : Row := { vars := #[285, 129, 359, 153, 162], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 272391, edges := #[⟨0, 1, 381⟩, ⟨0, 2, 55⟩, ⟨0, 3, 510⟩, ⟨0, 4, 500⟩, ⟨1, 2, 255⟩, ⟨1, 3, 24⟩, ⟨1, 4, 14⟩, ⟨2, 3, 193⟩, ⟨2, 4, 213⟩, ⟨3, 4, 141⟩], triples := #[] }
def er011_077 : Row := { vars := #[291, 31, 40, 194], coeff := #[1, 1, 1, 1], bound := 1, weight := 99357, edges := #[⟨0, 1, 418⟩, ⟨0, 2, 417⟩, ⟨0, 3, 458⟩, ⟨1, 2, 8⟩, ⟨1, 3, 82⟩, ⟨2, 3, 105⟩], triples := #[] }
def er011_078 : Row := { vars := #[293, 174, 361], coeff := #[1, 1, 1], bound := 1, weight := 31470, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 19⟩, ⟨1, 2, 233⟩], triples := #[] }
def er011_079 : Row := { vars := #[304, 342, 92], coeff := #[1, 1, 1], bound := 1, weight := 97958, edges := #[⟨0, 1, 91⟩, ⟨0, 2, 388⟩, ⟨1, 2, 340⟩], triples := #[] }
def er011_080 : Row := { vars := #[305, 41, 201], coeff := #[1, 1, 1], bound := 1, weight := 18290, edges := #[⟨0, 1, 405⟩, ⟨0, 2, 267⟩, ⟨1, 2, 400⟩], triples := #[] }
def er011_081 : Row := { vars := #[309, 394, 175], coeff := #[1, 1, 1], bound := 1, weight := 107418, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 461⟩, ⟨1, 2, 349⟩], triples := #[] }
def er011_082 : Row := { vars := #[310, 128, 348], coeff := #[1, 1, 1], bound := 1, weight := 35228, edges := #[⟨0, 1, 397⟩, ⟨0, 2, 126⟩, ⟨1, 2, 350⟩], triples := #[] }
def er011_083 : Row := { vars := #[311, 335, 380], coeff := #[1, 1, 1], bound := 1, weight := 235672, edges := #[⟨0, 1, 117⟩, ⟨0, 2, 54⟩, ⟨1, 2, 478⟩], triples := #[] }
def er011_084 : Row := { vars := #[322, 334, 40], coeff := #[1, 1, 1], bound := 1, weight := 321470, edges := #[⟨0, 1, 355⟩, ⟨0, 2, 237⟩, ⟨1, 2, 243⟩], triples := #[] }
def er011_085 : Row := { vars := #[324, 152, 242], coeff := #[1, 1, 1], bound := 1, weight := 47462, edges := #[⟨0, 1, 248⟩, ⟨0, 2, 148⟩, ⟨1, 2, 371⟩], triples := #[] }
def er011_086 : Row := { vars := #[324, 316, 335], coeff := #[1, 1, 1], bound := 1, weight := 425890, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 355⟩, ⟨1, 2, 371⟩], triples := #[] }
def er011_087 : Row := { vars := #[329, 325, 221], coeff := #[1, 1, 1], bound := 1, weight := 395154, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 54⟩, ⟨1, 2, 69⟩], triples := #[] }
def er011_088 : Row := { vars := #[329, 229, 33], coeff := #[1, 1, 1], bound := 1, weight := 156506, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 234⟩, ⟨1, 2, 380⟩], triples := #[] }
def er011_089 : Row := { vars := #[351, 260, 423], coeff := #[1, 1, 1], bound := 1, weight := 515762, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 439⟩, ⟨1, 2, 69⟩], triples := #[] }
def er011_090 : Row := { vars := #[351, 198, 31], coeff := #[1, 1, 1], bound := 1, weight := 104820, edges := #[⟨0, 1, 16⟩, ⟨0, 2, 193⟩, ⟨1, 2, 403⟩], triples := #[] }
def er011_091 : Row := { vars := #[357, 390, 364], coeff := #[1, 1, 1], bound := 1, weight := 182035, edges := #[⟨0, 1, 416⟩, ⟨0, 2, 449⟩, ⟨1, 2, 410⟩], triples := #[] }
def er011_092 : Row := { vars := #[367, 176, 223], coeff := #[1, 1, 1], bound := 1, weight := 82454, edges := #[⟨0, 1, 226⟩, ⟨0, 2, 176⟩, ⟨1, 2, 424⟩], triples := #[] }
def er011_093 : Row := { vars := #[368, 280, 62], coeff := #[1, 1, 1], bound := 1, weight := 33914, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 302⟩, ⟨1, 2, 425⟩], triples := #[] }
def er011_094 : Row := { vars := #[371, 423, 320], coeff := #[1, 1, 1], bound := 1, weight := 51261, edges := #[⟨0, 1, 359⟩, ⟨0, 2, 494⟩, ⟨1, 2, 432⟩], triples := #[] }
def er011_095 : Row := { vars := #[373, 217, 176], coeff := #[1, 1, 1], bound := 1, weight := 51312, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 231⟩, ⟨1, 2, 456⟩], triples := #[] }
def er011_096 : Row := { vars := #[374, 264, 217], coeff := #[1, 1, 1], bound := 1, weight := 466, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 188⟩, ⟨1, 2, 319⟩], triples := #[] }
def er011_097 : Row := { vars := #[381, 280, 33], coeff := #[1, 1, 1], bound := 1, weight := 174825, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 302⟩, ⟨1, 2, 445⟩], triples := #[] }
def er011_098 : Row := { vars := #[382, 209, 248], coeff := #[1, 1, 1], bound := 1, weight := 864903, edges := #[⟨0, 1, 174⟩, ⟨0, 2, 98⟩, ⟨1, 2, 351⟩], triples := #[] }
def er011_099 : Row := { vars := #[383, 191, 211], coeff := #[1, 1, 1], bound := 1, weight := 167440, edges := #[⟨0, 1, 238⟩, ⟨0, 2, 175⟩, ⟨1, 2, 423⟩], triples := #[] }
def er011_100 : Row := { vars := #[384, 402, 334], coeff := #[1, 1, 1], bound := 1, weight := 132789, edges := #[⟨0, 1, 373⟩, ⟨0, 2, 470⟩, ⟨1, 2, 448⟩], triples := #[] }
def er011_101 : Row := { vars := #[387, 402, 38], coeff := #[1, 1, 1], bound := 1, weight := 273018, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 305⟩, ⟨1, 2, 264⟩], triples := #[] }
def er011_102 : Row := { vars := #[388, 60, 175, 177], coeff := #[1, 1, 1, 1], bound := 1, weight := 9329, edges := #[⟨0, 1, 330⟩, ⟨0, 2, 199⟩, ⟨0, 3, 215⟩, ⟨1, 2, 95⟩, ⟨1, 3, 82⟩, ⟨2, 3, 171⟩], triples := #[] }
def er011_103 : Row := { vars := #[397, 199, 89], coeff := #[1, 1, 1], bound := 1, weight := 311836, edges := #[⟨0, 1, 88⟩, ⟨0, 2, 194⟩, ⟨1, 2, 467⟩], triples := #[] }
def er011_104 : Row := { vars := #[404, 298, 380], coeff := #[1, 1, 1], bound := 1, weight := 165907, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 375⟩, ⟨1, 2, 47⟩], triples := #[] }
def er011_105 : Row := { vars := #[409, 133, 217], coeff := #[1, 1, 1], bound := 1, weight := 220708, edges := #[⟨0, 1, 212⟩, ⟨0, 2, 131⟩, ⟨1, 2, 486⟩], triples := #[] }
def er011_106 : Row := { vars := #[409, 283, 40, 31], coeff := #[1, 1, 1, 1], bound := 1, weight := 377579, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 267⟩, ⟨0, 3, 256⟩, ⟨1, 2, 423⟩, ⟨1, 3, 433⟩, ⟨2, 3, 8⟩], triples := #[] }
def er011_107 : Row := { vars := #[409, 31, 40, 34], coeff := #[1, 1, 1, 1], bound := 1, weight := 96767, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 267⟩, ⟨0, 3, 254⟩, ⟨1, 2, 8⟩, ⟨1, 3, 25⟩, ⟨2, 3, 15⟩], triples := #[] }
def er011_108 : Row := { vars := #[409, 175, 319], coeff := #[1, 1, 1], bound := 1, weight := 304948, edges := #[⟨0, 1, 308⟩, ⟨0, 2, 440⟩, ⟨1, 2, 297⟩], triples := #[] }
def er011_109 : Row := { vars := #[419, 286, 212], coeff := #[1, 1, 1], bound := 1, weight := 11914, edges := #[⟨0, 1, 159⟩, ⟨0, 2, 114⟩, ⟨1, 2, 295⟩], triples := #[] }
def er011_110 : Row := { vars := #[419, 177, 200], coeff := #[1, 1, 1], bound := 1, weight := 89114, edges := #[⟨0, 1, 300⟩, ⟨0, 2, 116⟩, ⟨1, 2, 446⟩], triples := #[] }
def er011_111 : Row := { vars := #[422, 260, 193], coeff := #[1, 1, 1], bound := 1, weight := 72521, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 331⟩, ⟨1, 2, 400⟩], triples := #[] }
def er011_112 : Row := { vars := #[422, 264, 211], coeff := #[1, 1, 1], bound := 1, weight := 90134, edges := #[⟨0, 1, 64⟩, ⟨0, 2, 113⟩, ⟨1, 2, 326⟩], triples := #[] }
def er011_113 : Row := { vars := #[426, 274, 204], coeff := #[1, 1, 1], bound := 1, weight := 226676, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 115⟩, ⟨1, 2, 317⟩], triples := #[] }
def er011_114 : Row := { vars := #[0, 23, 54, 131, 260, 376], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 35393, edges := #[⟨3, 4, 448⟩, ⟨3, 5, 288⟩, ⟨4, 5, 122⟩, ⟨0, 3, 175⟩, ⟨1, 3, 149⟩, ⟨0, 4, 468⟩, ⟨2, 4, 492⟩, ⟨0, 5, 308⟩, ⟨2, 5, 332⟩], triples := #[⟨0, 1, 2⟩] }
def er011_115 : Row := { vars := #[0, 28, 65, 161, 297], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 9251, edges := #[⟨3, 4, 508⟩, ⟨0, 3, 89⟩, ⟨2, 3, 117⟩, ⟨0, 4, 440⟩, ⟨1, 4, 414⟩], triples := #[⟨0, 1, 2⟩] }
def er011_116 : Row := { vars := #[0, 28, 65, 344, 217], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 82346, edges := #[⟨3, 4, 70⟩, ⟨0, 3, 238⟩, ⟨2, 3, 212⟩, ⟨0, 4, 363⟩, ⟨2, 4, 391⟩], triples := #[⟨0, 1, 2⟩] }
def er011_117 : Row := { vars := #[0, 241, 397, 274, 199], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 8313, edges := #[⟨3, 4, 320⟩, ⟨0, 3, 472⟩, ⟨1, 3, 256⟩, ⟨0, 4, 357⟩, ⟨2, 4, 88⟩], triples := #[⟨0, 1, 2⟩] }
def er011_118 : Row := { vars := #[0, 243, 395, 264, 99, 362], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 21887, edges := #[⟨3, 4, 426⟩, ⟨3, 5, 83⟩, ⟨4, 5, 286⟩, ⟨0, 3, 470⟩, ⟨1, 3, 258⟩, ⟨0, 4, 148⟩, ⟨2, 4, 196⟩, ⟨0, 5, 331⟩, ⟨1, 5, 127⟩], triples := #[⟨0, 1, 2⟩] }
def er011_119 : Row := { vars := #[0, 253, 424, 263, 90, 362], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 157618, edges := #[⟨3, 4, 432⟩, ⟨3, 5, 86⟩, ⟨4, 5, 296⟩, ⟨0, 3, 471⟩, ⟨2, 3, 52⟩, ⟨0, 4, 160⟩, ⟨1, 4, 440⟩, ⟨0, 5, 331⟩, ⟨1, 5, 116⟩], triples := #[⟨0, 1, 2⟩] }
def er011_120 : Row := { vars := #[0, 270, 407, 33, 292, 249], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 80090, edges := #[⟨3, 4, 424⟩, ⟨3, 5, 488⟩, ⟨4, 5, 233⟩, ⟨0, 3, 63⟩, ⟨1, 3, 459⟩, ⟨0, 4, 449⟩, ⟨1, 4, 197⟩, ⟨0, 5, 492⟩, ⟨2, 5, 28⟩], triples := #[⟨0, 1, 2⟩] }
def er011_121 : Row := { vars := #[0, 272, 405, 31, 198, 254], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 321480, edges := #[⟨3, 4, 403⟩, ⟨3, 5, 480⟩, ⟨4, 5, 350⟩, ⟨0, 3, 65⟩, ⟨1, 3, 459⟩, ⟨0, 4, 358⟩, ⟨1, 4, 312⟩, ⟨0, 5, 503⟩, ⟨2, 5, 18⟩], triples := #[⟨0, 1, 2⟩] }
def er011_122 : Row := { vars := #[0, 281, 357, 400, 307, 153], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 211503, edges := #[⟨3, 4, 166⟩, ⟨3, 5, 351⟩, ⟨4, 5, 480⟩, ⟨0, 3, 277⟩, ⟨1, 3, 187⟩, ⟨0, 4, 427⟩, ⟨1, 4, 311⟩, ⟨0, 5, 100⟩, ⟨2, 5, 201⟩], triples := #[⟨0, 1, 2⟩] }
def er011_123 : Row := { vars := #[0, 291, 386, 260, 133, 127], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 17645, edges := #[⟨3, 4, 446⟩, ⟨3, 5, 456⟩, ⟨4, 5, 123⟩, ⟨0, 3, 468⟩, ⟨2, 3, 127⟩, ⟨0, 4, 173⟩, ⟨1, 4, 356⟩, ⟨0, 5, 179⟩, ⟨1, 5, 360⟩], triples := #[⟨0, 1, 2⟩] }
def er011_124 : Row := { vars := #[0, 308, 369, 413, 41, 38], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 54479, edges := #[⟨3, 4, 272⟩, ⟨3, 5, 274⟩, ⟨4, 5, 35⟩, ⟨0, 3, 280⟩, ⟨1, 3, 160⟩, ⟨0, 4, 52⟩, ⟨2, 4, 311⟩, ⟨0, 5, 55⟩, ⟨2, 5, 308⟩], triples := #[⟨0, 1, 2⟩] }
def er011_125 : Row := { vars := #[1, 20, 46, 33, 38, 345, 262], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 152859, edges := #[⟨3, 4, 8⟩, ⟨3, 5, 220⟩, ⟨3, 6, 467⟩, ⟨4, 5, 208⟩, ⟨4, 6, 464⟩, ⟨5, 6, 183⟩, ⟨0, 3, 62⟩, ⟨1, 3, 26⟩, ⟨0, 4, 54⟩, ⟨1, 4, 18⟩, ⟨0, 5, 224⟩, ⟨2, 5, 234⟩, ⟨0, 6, 469⟩, ⟨2, 6, 491⟩], triples := #[⟨0, 1, 2⟩] }
def er011_126 : Row := { vars := #[1, 20, 46, 67, 62, 337, 247], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 398801, edges := #[⟨3, 4, 44⟩, ⟨3, 5, 208⟩, ⟨3, 6, 464⟩, ⟨4, 5, 220⟩, ⟨4, 6, 467⟩, ⟨5, 6, 171⟩, ⟨0, 3, 18⟩, ⟨2, 3, 54⟩, ⟨0, 4, 26⟩, ⟨2, 4, 62⟩, ⟨0, 5, 234⟩, ⟨1, 5, 224⟩, ⟨0, 6, 491⟩, ⟨1, 6, 469⟩], triples := #[⟨0, 1, 2⟩] }
def er011_127 : Row := { vars := #[1, 205, 329, 317, 327], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 448342, edges := #[⟨3, 4, 380⟩, ⟨0, 3, 194⟩, ⟨2, 3, 362⟩, ⟨0, 4, 212⟩, ⟨2, 4, 356⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert


