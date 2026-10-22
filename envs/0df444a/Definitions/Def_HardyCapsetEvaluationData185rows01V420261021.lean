-- Prove2me | Definitions.Def_HardyCapsetEvaluationData185rows01V420261021
-- name    : HardyCapsetEvaluationData185rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:48:42.181993+00:00
-- url     : https://prove2.me/theorems/11d2c134-7c63-4ed9-85b1-951e1a757454
-- title:
--   HardyCapsetEvaluationData185rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er185_064 : Row := { vars := #[141, 170, 172], coeff := #[1, 1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 104⟩, ⟨1, 2, 358⟩], triples := #[] }
def er185_065 : Row := { vars := #[157, 261, 178], coeff := #[1, 1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 451⟩, ⟨0, 2, 370⟩, ⟨1, 2, 437⟩], triples := #[] }
def er185_066 : Row := { vars := #[170, 32, 206], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 301⟩, ⟨0, 2, 461⟩, ⟨1, 2, 251⟩], triples := #[] }
def er185_067 : Row := { vars := #[171, 211, 258], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 441⟩, ⟨1, 2, 385⟩], triples := #[] }
def er185_068 : Row := { vars := #[174, 275, 260], coeff := #[1, 1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 443⟩, ⟨1, 2, 458⟩], triples := #[] }
def er185_069 : Row := { vars := #[199, 20, 232], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 241⟩, ⟨0, 2, 495⟩, ⟨1, 2, 335⟩], triples := #[] }
def er185_070 : Row := { vars := #[210, 177, 217], coeff := #[1, 1, 1], bound := 1, weight := 464286, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 431⟩, ⟨1, 2, 491⟩], triples := #[] }
def er185_071 : Row := { vars := #[233, 280, 59], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 195⟩, ⟨1, 2, 305⟩], triples := #[] }
def er185_072 : Row := { vars := #[278, 52, 55], coeff := #[1, 1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 313⟩, ⟨0, 2, 317⟩, ⟨1, 2, 162⟩], triples := #[] }
def er185_073 : Row := { vars := #[0, 82, 166, 193, 24], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 892858, edges := #[⟨3, 4, 212⟩, ⟨0, 3, 237⟩, ⟨1, 3, 64⟩, ⟨0, 4, 13⟩, ⟨2, 4, 230⟩], triples := #[⟨0, 1, 2⟩] }
def er185_074 : Row := { vars := #[0, 83, 169, 43], coeff := #[1, 1, 1, 1], bound := 2, weight := 53572, edges := #[⟨0, 3, 179⟩, ⟨2, 3, 311⟩], triples := #[⟨0, 1, 2⟩] }
def er185_075 : Row := { vars := #[0, 108, 191, 207, 23], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨3, 4, 321⟩, ⟨0, 3, 301⟩, ⟨1, 3, 178⟩, ⟨0, 4, 14⟩, ⟨2, 4, 209⟩], triples := #[⟨0, 1, 2⟩] }
def er185_076 : Row := { vars := #[0, 144, 205, 200, 57], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 285715, edges := #[⟨3, 4, 267⟩, ⟨0, 3, 227⟩, ⟨1, 3, 119⟩, ⟨0, 4, 86⟩, ⟨2, 4, 210⟩], triples := #[⟨0, 1, 2⟩] }
def er185_077 : Row := { vars := #[0, 156, 212, 268, 240], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 356⟩, ⟨0, 3, 279⟩, ⟨1, 3, 160⟩, ⟨0, 4, 317⟩, ⟨2, 4, 413⟩], triples := #[⟨0, 1, 2⟩] }
def er185_078 : Row := { vars := #[1, 81, 186, 190, 17], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 696429, edges := #[⟨3, 4, 193⟩, ⟨0, 3, 238⟩, ⟨1, 3, 53⟩, ⟨0, 4, 24⟩, ⟨2, 4, 230⟩], triples := #[⟨0, 1, 2⟩] }
def er185_079 : Row := { vars := #[2, 78, 202, 189], coeff := #[1, 1, 1, 1], bound := 2, weight := 17858, edges := #[⟨0, 3, 226⟩, ⟨2, 3, 366⟩], triples := #[⟨0, 1, 2⟩] }
def er185_080 : Row := { vars := #[4, 99, 162, 144], coeff := #[1, 1, 1, 1], bound := 2, weight := 410715, edges := #[⟨1, 3, 258⟩, ⟨2, 3, 89⟩], triples := #[⟨0, 1, 2⟩] }
def er185_081 : Row := { vars := #[6, 137, 231, 27], coeff := #[1, 1, 1, 1], bound := 2, weight := 214286, edges := #[⟨1, 3, 356⟩, ⟨2, 3, 257⟩], triples := #[⟨0, 1, 2⟩] }
def er185_082 : Row := { vars := #[9, 111, 280, 143, 18], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨3, 4, 426⟩, ⟨0, 3, 453⟩, ⟨2, 3, 170⟩, ⟨1, 4, 468⟩, ⟨2, 4, 297⟩], triples := #[⟨0, 1, 2⟩] }
def er185_083 : Row := { vars := #[9, 115, 277, 256, 172], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨3, 4, 448⟩, ⟨0, 3, 264⟩, ⟨2, 3, 459⟩, ⟨1, 4, 141⟩, ⟨2, 4, 420⟩], triples := #[⟨0, 1, 2⟩] }
def er185_084 : Row := { vars := #[10, 135, 235, 17, 119], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 303572, edges := #[⟨3, 4, 480⟩, ⟨1, 3, 414⟩, ⟨2, 3, 350⟩, ⟨0, 4, 506⟩, ⟨2, 4, 110⟩], triples := #[⟨0, 1, 2⟩] }
def er185_085 : Row := { vars := #[11, 118, 289, 47], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨1, 3, 361⟩, ⟨2, 3, 312⟩], triples := #[⟨0, 1, 2⟩] }
def er185_086 : Row := { vars := #[15, 72, 193, 120], coeff := #[1, 1, 1, 1], bound := 2, weight := 17858, edges := #[⟨1, 3, 301⟩, ⟨2, 3, 191⟩], triples := #[⟨0, 1, 2⟩] }
def er185_087 : Row := { vars := #[15, 91, 180, 120], coeff := #[1, 1, 1, 1], bound := 2, weight := 232143, edges := #[⟨1, 3, 333⟩, ⟨2, 3, 160⟩], triples := #[⟨0, 1, 2⟩] }
def er185_088 : Row := { vars := #[21, 111, 263, 6, 142], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 785715, edges := #[⟨3, 4, 448⟩, ⟨1, 3, 490⟩, ⟨2, 3, 274⟩, ⟨0, 4, 430⟩, ⟨2, 4, 182⟩], triples := #[⟨0, 1, 2⟩] }
def er185_089 : Row := { vars := #[22, 135, 218, 242, 159], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 696429, edges := #[⟨3, 4, 480⟩, ⟨0, 3, 350⟩, ⟨2, 3, 404⟩, ⟨1, 4, 80⟩, ⟨2, 4, 506⟩], triples := #[⟨0, 1, 2⟩] }
def er185_090 : Row := { vars := #[22, 139, 215, 11, 113], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 303572, edges := #[⟨3, 4, 502⟩, ⟨1, 3, 436⟩, ⟨2, 3, 317⟩, ⟨0, 4, 473⟩, ⟨2, 4, 122⟩], triples := #[⟨0, 1, 2⟩] }
def er185_091 : Row := { vars := #[30, 88, 276, 38], coeff := #[1, 1, 1, 1], bound := 2, weight := 714286, edges := #[⟨1, 3, 471⟩, ⟨2, 3, 197⟩], triples := #[⟨0, 1, 2⟩] }
def er185_092 : Row := { vars := #[30, 114, 205, 57], coeff := #[1, 1, 1, 1], bound := 2, weight := 285715, edges := #[⟨1, 3, 371⟩, ⟨2, 3, 210⟩], triples := #[⟨0, 1, 2⟩] }
def er185_093 : Row := { vars := #[31, 138, 169, 64], coeff := #[1, 1, 1, 1], bound := 2, weight := 107143, edges := #[⟨1, 3, 474⟩, ⟨2, 3, 260⟩], triples := #[⟨0, 1, 2⟩] }
def er185_094 : Row := { vars := #[33, 87, 281, 106, 51], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 678572, edges := #[⟨3, 4, 426⟩, ⟨0, 3, 485⟩, ⟨2, 3, 123⟩, ⟨1, 4, 437⟩, ⟨2, 4, 329⟩], triples := #[⟨0, 1, 2⟩] }
def er185_095 : Row := { vars := #[34, 99, 261, 50, 94], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 267858, edges := #[⟨3, 4, 448⟩, ⟨1, 3, 415⟩, ⟨2, 3, 349⟩, ⟨0, 4, 505⟩, ⟨2, 4, 111⟩], triples := #[⟨0, 1, 2⟩] }
def er185_096 : Row := { vars := #[36, 119, 209, 48], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨1, 3, 363⟩, ⟨2, 3, 201⟩], triples := #[⟨0, 1, 2⟩] }
def er185_097 : Row := { vars := #[37, 143, 188, 50], coeff := #[1, 1, 1, 1], bound := 2, weight := 160715, edges := #[⟨1, 3, 464⟩, ⟨2, 3, 250⟩], triples := #[⟨0, 1, 2⟩] }
def er185_098 : Row := { vars := #[38, 66, 275, 83], coeff := #[1, 1, 1, 1], bound := 2, weight := 107143, edges := #[⟨1, 3, 203⟩, ⟨2, 3, 113⟩], triples := #[⟨0, 1, 2⟩] }
def er185_099 : Row := { vars := #[39, 139, 200, 0, 25], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 53572, edges := #[⟨3, 4, 15⟩, ⟨0, 3, 191⟩, ⟨2, 3, 227⟩, ⟨1, 4, 415⟩, ⟨2, 4, 241⟩], triples := #[⟨0, 1, 2⟩] }
def er185_100 : Row := { vars := #[40, 68, 281, 274, 180], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 321429, edges := #[⟨3, 4, 426⟩, ⟨1, 3, 111⟩, ⟨2, 3, 505⟩, ⟨0, 4, 349⟩, ⟨2, 4, 415⟩], triples := #[⟨0, 1, 2⟩] }
def er185_101 : Row := { vars := #[40, 73, 278, 114, 23], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨3, 4, 480⟩, ⟨0, 3, 441⟩, ⟨2, 3, 9⟩, ⟨1, 4, 385⟩, ⟨2, 4, 285⟩], triples := #[⟨0, 1, 2⟩] }
def er185_102 : Row := { vars := #[42, 87, 249, 84], coeff := #[1, 1, 1, 1], bound := 2, weight := 357143, edges := #[⟨1, 3, 238⟩, ⟨2, 3, 88⟩], triples := #[⟨0, 1, 2⟩] }
def er185_103 : Row := { vars := #[44, 74, 258, 163, 267], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 448⟩, ⟨0, 3, 319⟩, ⟨2, 3, 437⟩, ⟨1, 4, 123⟩, ⟨2, 4, 475⟩], triples := #[⟨0, 1, 2⟩] }
def er185_104 : Row := { vars := #[45, 66, 263, 106, 51], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 321429, edges := #[⟨3, 4, 426⟩, ⟨0, 3, 506⟩, ⟨2, 3, 80⟩, ⟨1, 4, 404⟩, ⟨2, 4, 350⟩], triples := #[⟨0, 1, 2⟩] }
def er185_105 : Row := { vars := #[45, 71, 260, 101, 57], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 428572, edges := #[⟨3, 4, 426⟩, ⟨0, 3, 496⟩, ⟨2, 3, 80⟩, ⟨1, 4, 404⟩, ⟨2, 4, 340⟩], triples := #[⟨0, 1, 2⟩] }
def er185_106 : Row := { vars := #[47, 69, 204, 96], coeff := #[1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨1, 3, 238⟩, ⟨2, 3, 184⟩], triples := #[⟨0, 1, 2⟩] }
def er185_107 : Row := { vars := #[53, 91, 234, 100, 37], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 428572, edges := #[⟨3, 4, 480⟩, ⟨0, 3, 421⟩, ⟨2, 3, 183⟩, ⟨1, 4, 491⟩, ⟨2, 4, 265⟩], triples := #[⟨0, 1, 2⟩] }
def er185_108 : Row := { vars := #[54, 103, 214, 36, 88], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 502⟩, ⟨1, 3, 469⟩, ⟨2, 3, 285⟩, ⟨0, 4, 441⟩, ⟨2, 4, 171⟩], triples := #[⟨0, 1, 2⟩] }
def er185_109 : Row := { vars := #[55, 75, 203, 112], coeff := #[1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨1, 3, 305⟩, ⟨2, 3, 74⟩], triples := #[⟨0, 1, 2⟩] }
def er185_110 : Row := { vars := #[59, 111, 197, 82], coeff := #[1, 1, 1, 1], bound := 2, weight := 17858, edges := #[⟨1, 3, 302⟩, ⟨2, 3, 16⟩], triples := #[⟨0, 1, 2⟩] }
def er185_111 : Row := { vars := #[59, 115, 200, 0, 25], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨3, 4, 15⟩, ⟨0, 3, 131⟩, ⟨2, 3, 227⟩, ⟨1, 4, 469⟩, ⟨2, 4, 241⟩], triples := #[⟨0, 1, 2⟩] }
def er185_112 : Row := { vars := #[60, 68, 237, 143, 18], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 321429, edges := #[⟨3, 4, 426⟩, ⟨0, 3, 505⟩, ⟨2, 3, 8⟩, ⟨1, 4, 384⟩, ⟨2, 4, 349⟩], triples := #[⟨0, 1, 2⟩] }
def er185_113 : Row := { vars := #[60, 73, 234, 35], coeff := #[1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨1, 3, 459⟩, ⟨2, 3, 264⟩], triples := #[⟨0, 1, 2⟩] }
def er185_114 : Row := { vars := #[61, 72, 232, 25], coeff := #[1, 1, 1, 1], bound := 2, weight := 285715, edges := #[⟨1, 3, 384⟩, ⟨2, 3, 339⟩], triples := #[⟨0, 1, 2⟩] }
def er185_115 : Row := { vars := #[62, 72, 223, 84], coeff := #[1, 1, 1, 1], bound := 2, weight := 642858, edges := #[⟨1, 3, 196⟩, ⟨2, 3, 191⟩], triples := #[⟨0, 1, 2⟩] }
def er185_116 : Row := { vars := #[62, 124, 179, 0, 56], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 17858, edges := #[⟨3, 4, 87⟩, ⟨0, 3, 118⟩, ⟨2, 3, 197⟩, ⟨1, 4, 395⟩, ⟨2, 4, 251⟩], triples := #[⟨0, 1, 2⟩] }
def er185_117 : Row := { vars := #[64, 69, 217, 177, 210], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨3, 4, 502⟩, ⟨0, 3, 275⟩, ⟨2, 3, 491⟩, ⟨1, 4, 183⟩, ⟨2, 4, 431⟩], triples := #[⟨0, 1, 2⟩] }
def er185_118 : Row := { vars := #[65, 67, 218, 105, 31], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 750001, edges := #[⟨3, 4, 480⟩, ⟨0, 3, 453⟩, ⟨2, 3, 140⟩, ⟨1, 4, 458⟩, ⟨2, 4, 297⟩], triples := #[⟨0, 1, 2⟩] }
def er185_119 : Row := { vars := #[67, 85, 102, 175, 196], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 107143, edges := #[⟨3, 4, 388⟩, ⟨1, 3, 53⟩, ⟨2, 3, 22⟩, ⟨0, 4, 8⟩, ⟨2, 4, 40⟩], triples := #[⟨0, 1, 2⟩] }
def er185_120 : Row := { vars := #[67, 113, 134, 201], coeff := #[1, 1, 1, 1], bound := 2, weight := 142858, edges := #[⟨0, 3, 20⟩, ⟨1, 3, 173⟩], triples := #[⟨0, 1, 2⟩] }
def er185_121 : Row := { vars := #[68, 110, 136, 201], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨0, 3, 22⟩, ⟨2, 3, 112⟩], triples := #[⟨0, 1, 2⟩] }
def er185_122 : Row := { vars := #[68, 110, 136, 175, 229], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 472⟩, ⟨1, 3, 148⟩, ⟨2, 3, 92⟩, ⟨0, 4, 171⟩, ⟨2, 4, 3⟩], triples := #[⟨0, 1, 2⟩] }
def er185_123 : Row := { vars := #[72, 119, 133, 194], coeff := #[1, 1, 1, 1], bound := 2, weight := 53572, edges := #[⟨0, 3, 41⟩, ⟨1, 3, 191⟩], triples := #[⟨0, 1, 2⟩] }
def er185_124 : Row := { vars := #[75, 76, 77, 129, 130], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 290⟩, ⟨0, 3, 324⟩, ⟨1, 3, 323⟩, ⟨0, 4, 314⟩, ⟨1, 4, 313⟩], triples := #[⟨0, 1, 2⟩] }
def er185_125 : Row := { vars := #[75, 78, 79, 153, 154], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 982143, edges := #[⟨3, 4, 344⟩, ⟨0, 3, 269⟩, ⟨2, 3, 271⟩, ⟨0, 4, 259⟩, ⟨2, 4, 261⟩], triples := #[⟨0, 1, 2⟩] }
def er185_126 : Row := { vars := #[75, 92, 104, 147, 148], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 322⟩, ⟨0, 3, 292⟩, ⟨1, 3, 271⟩, ⟨0, 4, 282⟩, ⟨1, 4, 261⟩], triples := #[⟨0, 1, 2⟩] }
def er185_127 : Row := { vars := #[75, 116, 140, 153, 154], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 17858, edges := #[⟨3, 4, 344⟩, ⟨0, 3, 269⟩, ⟨2, 3, 323⟩, ⟨0, 4, 259⟩, ⟨2, 4, 313⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert


