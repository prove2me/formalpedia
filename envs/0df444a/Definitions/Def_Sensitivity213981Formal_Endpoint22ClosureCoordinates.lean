-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureCoordinates
-- name    : Sensitivity213981Formal_Endpoint22ClosureCoordinates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:11:08.838605+00:00
-- url     : https://prove2.me/theorems/fb8db01a-4338-4f5d-ba0e-1f62bb46aac1
-- title:
--   Endpoint22 Closure Coordinates — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Closure Coordinates in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.coordinateTable`, `ThreeBoundMinmaxNumeric.Endpoint22.coordOfIndex`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ClosureCoordinates.lean, lines 1–5487.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate
def coordinateTable:Table (Coord 22):=
(.branch 1369
(.branch 684
(.branch 342
(.branch 171
(.branch 85
(.branch 42
(.branch 21
(.branch 10
(.branch 5
(.branch 2
(.branch 1
(.leaf (.a 0 0))
(.leaf (.a 0 1)))
(.branch 3
(.leaf (.a 0 2))
(.branch 4
(.leaf (.a 0 3))
(.leaf (.a 0 4)))))
(.branch 7
(.branch 6
(.leaf (.a 0 5))
(.leaf (.a 0 6)))
(.branch 8
(.leaf (.a 0 7))
(.branch 9
(.leaf (.a 0 8))
(.leaf (.a 0 9))))))
(.branch 15
(.branch 12
(.branch 11
(.leaf (.a 0 10))
(.leaf (.a 0 11)))
(.branch 13
(.leaf (.a 0 12))
(.branch 14
(.leaf (.a 0 13))
(.leaf (.a 0 14)))))
(.branch 18
(.branch 16
(.leaf (.a 0 15))
(.branch 17
(.leaf (.a 0 16))
(.leaf (.a 0 17))))
(.branch 19
(.leaf (.a 0 18))
(.branch 20
(.leaf (.a 0 19))
(.leaf (.a 0 20)))))))
(.branch 31
(.branch 26
(.branch 23
(.branch 22
(.leaf (.a 0 21))
(.leaf (.a 1 1)))
(.branch 24
(.leaf (.a 1 2))
(.branch 25
(.leaf (.a 1 3))
(.leaf (.a 1 4)))))
(.branch 28
(.branch 27
(.leaf (.a 1 5))
(.leaf (.a 1 6)))
(.branch 29
(.leaf (.a 1 7))
(.branch 30
(.leaf (.a 1 8))
(.leaf (.a 1 9))))))
(.branch 36
(.branch 33
(.branch 32
(.leaf (.a 1 10))
(.leaf (.a 1 11)))
(.branch 34
(.leaf (.a 1 12))
(.branch 35
(.leaf (.a 1 13))
(.leaf (.a 1 14)))))
(.branch 39
(.branch 37
(.leaf (.a 1 15))
(.branch 38
(.leaf (.a 1 16))
(.leaf (.a 1 17))))
(.branch 40
(.leaf (.a 1 18))
(.branch 41
(.leaf (.a 1 19))
(.leaf (.a 1 20))))))))
(.branch 63
(.branch 52
(.branch 47
(.branch 44
(.branch 43
(.leaf (.a 1 21))
(.leaf (.a 2 2)))
(.branch 45
(.leaf (.a 2 3))
(.branch 46
(.leaf (.a 2 4))
(.leaf (.a 2 5)))))
(.branch 49
(.branch 48
(.leaf (.a 2 6))
(.leaf (.a 2 7)))
(.branch 50
(.leaf (.a 2 8))
(.branch 51
(.leaf (.a 2 9))
(.leaf (.a 2 10))))))
(.branch 57
(.branch 54
(.branch 53
(.leaf (.a 2 11))
(.leaf (.a 2 12)))
(.branch 55
(.leaf (.a 2 13))
(.branch 56
(.leaf (.a 2 14))
(.leaf (.a 2 15)))))
(.branch 60
(.branch 58
(.leaf (.a 2 16))
(.branch 59
(.leaf (.a 2 17))
(.leaf (.a 2 18))))
(.branch 61
(.leaf (.a 2 19))
(.branch 62
(.leaf (.a 2 20))
(.leaf (.a 2 21)))))))
(.branch 74
(.branch 68
(.branch 65
(.branch 64
(.leaf (.a 3 3))
(.leaf (.a 3 4)))
(.branch 66
(.leaf (.a 3 5))
(.branch 67
(.leaf (.a 3 6))
(.leaf (.a 3 7)))))
(.branch 71
(.branch 69
(.leaf (.a 3 8))
(.branch 70
(.leaf (.a 3 9))
(.leaf (.a 3 10))))
(.branch 72
(.leaf (.a 3 11))
(.branch 73
(.leaf (.a 3 12))
(.leaf (.a 3 13))))))
(.branch 79
(.branch 76
(.branch 75
(.leaf (.a 3 14))
(.leaf (.a 3 15)))
(.branch 77
(.leaf (.a 3 16))
(.branch 78
(.leaf (.a 3 17))
(.leaf (.a 3 18)))))
(.branch 82
(.branch 80
(.leaf (.a 3 19))
(.branch 81
(.leaf (.a 3 20))
(.leaf (.a 3 21))))
(.branch 83
(.leaf (.a 4 4))
(.branch 84
(.leaf (.a 4 5))
(.leaf (.a 4 6)))))))))
(.branch 128
(.branch 106
(.branch 95
(.branch 90
(.branch 87
(.branch 86
(.leaf (.a 4 7))
(.leaf (.a 4 8)))
(.branch 88
(.leaf (.a 4 9))
(.branch 89
(.leaf (.a 4 10))
(.leaf (.a 4 11)))))
(.branch 92
(.branch 91
(.leaf (.a 4 12))
(.leaf (.a 4 13)))
(.branch 93
(.leaf (.a 4 14))
(.branch 94
(.leaf (.a 4 15))
(.leaf (.a 4 16))))))
(.branch 100
(.branch 97
(.branch 96
(.leaf (.a 4 17))
(.leaf (.a 4 18)))
(.branch 98
(.leaf (.a 4 19))
(.branch 99
(.leaf (.a 4 20))
(.leaf (.a 4 21)))))
(.branch 103
(.branch 101
(.leaf (.a 5 5))
(.branch 102
(.leaf (.a 5 6))
(.leaf (.a 5 7))))
(.branch 104
(.leaf (.a 5 8))
(.branch 105
(.leaf (.a 5 9))
(.leaf (.a 5 10)))))))
(.branch 117
(.branch 111
(.branch 108
(.branch 107
(.leaf (.a 5 11))
(.leaf (.a 5 12)))
(.branch 109
(.leaf (.a 5 13))
(.branch 110
(.leaf (.a 5 14))
(.leaf (.a 5 15)))))
(.branch 114
(.branch 112
(.leaf (.a 5 16))
(.branch 113
(.leaf (.a 5 17))
(.leaf (.a 5 18))))
(.branch 115
(.leaf (.a 5 19))
(.branch 116
(.leaf (.a 5 20))
(.leaf (.a 5 21))))))
(.branch 122
(.branch 119
(.branch 118
(.leaf (.a 6 6))
(.leaf (.a 6 7)))
(.branch 120
(.leaf (.a 6 8))
(.branch 121
(.leaf (.a 6 9))
(.leaf (.a 6 10)))))
(.branch 125
(.branch 123
(.leaf (.a 6 11))
(.branch 124
(.leaf (.a 6 12))
(.leaf (.a 6 13))))
(.branch 126
(.leaf (.a 6 14))
(.branch 127
(.leaf (.a 6 15))
(.leaf (.a 6 16))))))))
(.branch 149
(.branch 138
(.branch 133
(.branch 130
(.branch 129
(.leaf (.a 6 17))
(.leaf (.a 6 18)))
(.branch 131
(.leaf (.a 6 19))
(.branch 132
(.leaf (.a 6 20))
(.leaf (.a 6 21)))))
(.branch 135
(.branch 134
(.leaf (.a 7 7))
(.leaf (.a 7 8)))
(.branch 136
(.leaf (.a 7 9))
(.branch 137
(.leaf (.a 7 10))
(.leaf (.a 7 11))))))
(.branch 143
(.branch 140
(.branch 139
(.leaf (.a 7 12))
(.leaf (.a 7 13)))
(.branch 141
(.leaf (.a 7 14))
(.branch 142
(.leaf (.a 7 15))
(.leaf (.a 7 16)))))
(.branch 146
(.branch 144
(.leaf (.a 7 17))
(.branch 145
(.leaf (.a 7 18))
(.leaf (.a 7 19))))
(.branch 147
(.leaf (.a 7 20))
(.branch 148
(.leaf (.a 7 21))
(.leaf (.a 8 8)))))))
(.branch 160
(.branch 154
(.branch 151
(.branch 150
(.leaf (.a 8 9))
(.leaf (.a 8 10)))
(.branch 152
(.leaf (.a 8 11))
(.branch 153
(.leaf (.a 8 12))
(.leaf (.a 8 13)))))
(.branch 157
(.branch 155
(.leaf (.a 8 14))
(.branch 156
(.leaf (.a 8 15))
(.leaf (.a 8 16))))
(.branch 158
(.leaf (.a 8 17))
(.branch 159
(.leaf (.a 8 18))
(.leaf (.a 8 19))))))
(.branch 165
(.branch 162
(.branch 161
(.leaf (.a 8 20))
(.leaf (.a 8 21)))
(.branch 163
(.leaf (.a 9 9))
(.branch 164
(.leaf (.a 9 10))
(.leaf (.a 9 11)))))
(.branch 168
(.branch 166
(.leaf (.a 9 12))
(.branch 167
(.leaf (.a 9 13))
(.leaf (.a 9 14))))
(.branch 169
(.leaf (.a 9 15))
(.branch 170
(.leaf (.a 9 16))
(.leaf (.a 9 17))))))))))
(.branch 256
(.branch 213
(.branch 192
(.branch 181
(.branch 176
(.branch 173
(.branch 172
(.leaf (.a 9 18))
(.leaf (.a 9 19)))
(.branch 174
(.leaf (.a 9 20))
(.branch 175
(.leaf (.a 9 21))
(.leaf (.a 10 10)))))
(.branch 178
(.branch 177
(.leaf (.a 10 11))
(.leaf (.a 10 12)))
(.branch 179
(.leaf (.a 10 13))
(.branch 180
(.leaf (.a 10 14))
(.leaf (.a 10 15))))))
(.branch 186
(.branch 183
(.branch 182
(.leaf (.a 10 16))
(.leaf (.a 10 17)))
(.branch 184
(.leaf (.a 10 18))
(.branch 185
(.leaf (.a 10 19))
(.leaf (.a 10 20)))))
(.branch 189
(.branch 187
(.leaf (.a 10 21))
(.branch 188
(.leaf (.a 11 11))
(.leaf (.a 11 12))))
(.branch 190
(.leaf (.a 11 13))
(.branch 191
(.leaf (.a 11 14))
(.leaf (.a 11 15)))))))
(.branch 202
(.branch 197
(.branch 194
(.branch 193
(.leaf (.a 11 16))
(.leaf (.a 11 17)))
(.branch 195
(.leaf (.a 11 18))
(.branch 196
(.leaf (.a 11 19))
(.leaf (.a 11 20)))))
(.branch 199
(.branch 198
(.leaf (.a 11 21))
(.leaf (.a 12 12)))
(.branch 200
(.leaf (.a 12 13))
(.branch 201
(.leaf (.a 12 14))
(.leaf (.a 12 15))))))
(.branch 207
(.branch 204
(.branch 203
(.leaf (.a 12 16))
(.leaf (.a 12 17)))
(.branch 205
(.leaf (.a 12 18))
(.branch 206
(.leaf (.a 12 19))
(.leaf (.a 12 20)))))
(.branch 210
(.branch 208
(.leaf (.a 12 21))
(.branch 209
(.leaf (.a 13 13))
(.leaf (.a 13 14))))
(.branch 211
(.leaf (.a 13 15))
(.branch 212
(.leaf (.a 13 16))
(.leaf (.a 13 17))))))))
(.branch 234
(.branch 223
(.branch 218
(.branch 215
(.branch 214
(.leaf (.a 13 18))
(.leaf (.a 13 19)))
(.branch 216
(.leaf (.a 13 20))
(.branch 217
(.leaf (.a 13 21))
(.leaf (.a 14 14)))))
(.branch 220
(.branch 219
(.leaf (.a 14 15))
(.leaf (.a 14 16)))
(.branch 221
(.leaf (.a 14 17))
(.branch 222
(.leaf (.a 14 18))
(.leaf (.a 14 19))))))
(.branch 228
(.branch 225
(.branch 224
(.leaf (.a 14 20))
(.leaf (.a 14 21)))
(.branch 226
(.leaf (.a 15 15))
(.branch 227
(.leaf (.a 15 16))
(.leaf (.a 15 17)))))
(.branch 231
(.branch 229
(.leaf (.a 15 18))
(.branch 230
(.leaf (.a 15 19))
(.leaf (.a 15 20))))
(.branch 232
(.leaf (.a 15 21))
(.branch 233
(.leaf (.a 16 16))
(.leaf (.a 16 17)))))))
(.branch 245
(.branch 239
(.branch 236
(.branch 235
(.leaf (.a 16 18))
(.leaf (.a 16 19)))
(.branch 237
(.leaf (.a 16 20))
(.branch 238
(.leaf (.a 16 21))
(.leaf (.a 17 17)))))
(.branch 242
(.branch 240
(.leaf (.a 17 18))
(.branch 241
(.leaf (.a 17 19))
(.leaf (.a 17 20))))
(.branch 243
(.leaf (.a 17 21))
(.branch 244
(.leaf (.a 18 18))
(.leaf (.a 18 19))))))
(.branch 250
(.branch 247
(.branch 246
(.leaf (.a 18 20))
(.leaf (.a 18 21)))
(.branch 248
(.leaf (.a 19 19))
(.branch 249
(.leaf (.a 19 20))
(.leaf (.a 19 21)))))
(.branch 253
(.branch 251
(.leaf (.a 20 20))
(.branch 252
(.leaf (.a 20 21))
(.leaf (.a 21 21))))
(.branch 254
(.leaf (.b 0 0))
(.branch 255
(.leaf (.b 0 1))
(.leaf (.b 0 2)))))))))
(.branch 299
(.branch 277
(.branch 266
(.branch 261
(.branch 258
(.branch 257
(.leaf (.b 0 3))
(.leaf (.b 0 4)))
(.branch 259
(.leaf (.b 0 5))
(.branch 260
(.leaf (.b 0 6))
(.leaf (.b 0 7)))))
(.branch 263
(.branch 262
(.leaf (.b 0 8))
(.leaf (.b 0 9)))
(.branch 264
(.leaf (.b 0 10))
(.branch 265
(.leaf (.b 0 11))
(.leaf (.b 0 12))))))
(.branch 271
(.branch 268
(.branch 267
(.leaf (.b 0 13))
(.leaf (.b 0 14)))
(.branch 269
(.leaf (.b 0 15))
(.branch 270
(.leaf (.b 0 16))
(.leaf (.b 0 17)))))
(.branch 274
(.branch 272
(.leaf (.b 0 18))
(.branch 273
(.leaf (.b 0 19))
(.leaf (.b 0 20))))
(.branch 275
(.leaf (.b 0 21))
(.branch 276
(.leaf (.b 1 1))
(.leaf (.b 1 2)))))))
(.branch 288
(.branch 282
(.branch 279
(.branch 278
(.leaf (.b 1 3))
(.leaf (.b 1 4)))
(.branch 280
(.leaf (.b 1 5))
(.branch 281
(.leaf (.b 1 6))
(.leaf (.b 1 7)))))
(.branch 285
(.branch 283
(.leaf (.b 1 8))
(.branch 284
(.leaf (.b 1 9))
(.leaf (.b 1 10))))
(.branch 286
(.leaf (.b 1 11))
(.branch 287
(.leaf (.b 1 12))
(.leaf (.b 1 13))))))
(.branch 293
(.branch 290
(.branch 289
(.leaf (.b 1 14))
(.leaf (.b 1 15)))
(.branch 291
(.leaf (.b 1 16))
(.branch 292
(.leaf (.b 1 17))
(.leaf (.b 1 18)))))
(.branch 296
(.branch 294
(.leaf (.b 1 19))
(.branch 295
(.leaf (.b 1 20))
(.leaf (.b 1 21))))
(.branch 297
(.leaf (.b 2 2))
(.branch 298
(.leaf (.b 2 3))
(.leaf (.b 2 4))))))))
(.branch 320
(.branch 309
(.branch 304
(.branch 301
(.branch 300
(.leaf (.b 2 5))
(.leaf (.b 2 6)))
(.branch 302
(.leaf (.b 2 7))
(.branch 303
(.leaf (.b 2 8))
(.leaf (.b 2 9)))))
(.branch 306
(.branch 305
(.leaf (.b 2 10))
(.leaf (.b 2 11)))
(.branch 307
(.leaf (.b 2 12))
(.branch 308
(.leaf (.b 2 13))
(.leaf (.b 2 14))))))
(.branch 314
(.branch 311
(.branch 310
(.leaf (.b 2 15))
(.leaf (.b 2 16)))
(.branch 312
(.leaf (.b 2 17))
(.branch 313
(.leaf (.b 2 18))
(.leaf (.b 2 19)))))
(.branch 317
(.branch 315
(.leaf (.b 2 20))
(.branch 316
(.leaf (.b 2 21))
(.leaf (.b 3 3))))
(.branch 318
(.leaf (.b 3 4))
(.branch 319
(.leaf (.b 3 5))
(.leaf (.b 3 6)))))))
(.branch 331
(.branch 325
(.branch 322
(.branch 321
(.leaf (.b 3 7))
(.leaf (.b 3 8)))
(.branch 323
(.leaf (.b 3 9))
(.branch 324
(.leaf (.b 3 10))
(.leaf (.b 3 11)))))
(.branch 328
(.branch 326
(.leaf (.b 3 12))
(.branch 327
(.leaf (.b 3 13))
(.leaf (.b 3 14))))
(.branch 329
(.leaf (.b 3 15))
(.branch 330
(.leaf (.b 3 16))
(.leaf (.b 3 17))))))
(.branch 336
(.branch 333
(.branch 332
(.leaf (.b 3 18))
(.leaf (.b 3 19)))
(.branch 334
(.leaf (.b 3 20))
(.branch 335
(.leaf (.b 3 21))
(.leaf (.b 4 4)))))
(.branch 339
(.branch 337
(.leaf (.b 4 5))
(.branch 338
(.leaf (.b 4 6))
(.leaf (.b 4 7))))
(.branch 340
(.leaf (.b 4 8))
(.branch 341
(.leaf (.b 4 9))
(.leaf (.b 4 10)))))))))))
(.branch 513
(.branch 427
(.branch 384
(.branch 363
(.branch 352
(.branch 347
(.branch 344
(.branch 343
(.leaf (.b 4 11))
(.leaf (.b 4 12)))
(.branch 345
(.leaf (.b 4 13))
(.branch 346
(.leaf (.b 4 14))
(.leaf (.b 4 15)))))
(.branch 349
(.branch 348
(.leaf (.b 4 16))
(.leaf (.b 4 17)))
(.branch 350
(.leaf (.b 4 18))
(.branch 351
(.leaf (.b 4 19))
(.leaf (.b 4 20))))))
(.branch 357
(.branch 354
(.branch 353
(.leaf (.b 4 21))
(.leaf (.b 5 5)))
(.branch 355
(.leaf (.b 5 6))
(.branch 356
(.leaf (.b 5 7))
(.leaf (.b 5 8)))))
(.branch 360
(.branch 358
(.leaf (.b 5 9))
(.branch 359
(.leaf (.b 5 10))
(.leaf (.b 5 11))))
(.branch 361
(.leaf (.b 5 12))
(.branch 362
(.leaf (.b 5 13))
(.leaf (.b 5 14)))))))
(.branch 373
(.branch 368
(.branch 365
(.branch 364
(.leaf (.b 5 15))
(.leaf (.b 5 16)))
(.branch 366
(.leaf (.b 5 17))
(.branch 367
(.leaf (.b 5 18))
(.leaf (.b 5 19)))))
(.branch 370
(.branch 369
(.leaf (.b 5 20))
(.leaf (.b 5 21)))
(.branch 371
(.leaf (.b 6 6))
(.branch 372
(.leaf (.b 6 7))
(.leaf (.b 6 8))))))
(.branch 378
(.branch 375
(.branch 374
(.leaf (.b 6 9))
(.leaf (.b 6 10)))
(.branch 376
(.leaf (.b 6 11))
(.branch 377
(.leaf (.b 6 12))
(.leaf (.b 6 13)))))
(.branch 381
(.branch 379
(.leaf (.b 6 14))
(.branch 380
(.leaf (.b 6 15))
(.leaf (.b 6 16))))
(.branch 382
(.leaf (.b 6 17))
(.branch 383
(.leaf (.b 6 18))
(.leaf (.b 6 19))))))))
(.branch 405
(.branch 394
(.branch 389
(.branch 386
(.branch 385
(.leaf (.b 6 20))
(.leaf (.b 6 21)))
(.branch 387
(.leaf (.b 7 7))
(.branch 388
(.leaf (.b 7 8))
(.leaf (.b 7 9)))))
(.branch 391
(.branch 390
(.leaf (.b 7 10))
(.leaf (.b 7 11)))
(.branch 392
(.leaf (.b 7 12))
(.branch 393
(.leaf (.b 7 13))
(.leaf (.b 7 14))))))
(.branch 399
(.branch 396
(.branch 395
(.leaf (.b 7 15))
(.leaf (.b 7 16)))
(.branch 397
(.leaf (.b 7 17))
(.branch 398
(.leaf (.b 7 18))
(.leaf (.b 7 19)))))
(.branch 402
(.branch 400
(.leaf (.b 7 20))
(.branch 401
(.leaf (.b 7 21))
(.leaf (.b 8 8))))
(.branch 403
(.leaf (.b 8 9))
(.branch 404
(.leaf (.b 8 10))
(.leaf (.b 8 11)))))))
(.branch 416
(.branch 410
(.branch 407
(.branch 406
(.leaf (.b 8 12))
(.leaf (.b 8 13)))
(.branch 408
(.leaf (.b 8 14))
(.branch 409
(.leaf (.b 8 15))
(.leaf (.b 8 16)))))
(.branch 413
(.branch 411
(.leaf (.b 8 17))
(.branch 412
(.leaf (.b 8 18))
(.leaf (.b 8 19))))
(.branch 414
(.leaf (.b 8 20))
(.branch 415
(.leaf (.b 8 21))
(.leaf (.b 9 9))))))
(.branch 421
(.branch 418
(.branch 417
(.leaf (.b 9 10))
(.leaf (.b 9 11)))
(.branch 419
(.leaf (.b 9 12))
(.branch 420
(.leaf (.b 9 13))
(.leaf (.b 9 14)))))
(.branch 424
(.branch 422
(.leaf (.b 9 15))
(.branch 423
(.leaf (.b 9 16))
(.leaf (.b 9 17))))
(.branch 425
(.leaf (.b 9 18))
(.branch 426
(.leaf (.b 9 19))
(.leaf (.b 9 20)))))))))
(.branch 470
(.branch 448
(.branch 437
(.branch 432
(.branch 429
(.branch 428
(.leaf (.b 9 21))
(.leaf (.b 10 10)))
(.branch 430
(.leaf (.b 10 11))
(.branch 431
(.leaf (.b 10 12))
(.leaf (.b 10 13)))))
(.branch 434
(.branch 433
(.leaf (.b 10 14))
(.leaf (.b 10 15)))
(.branch 435
(.leaf (.b 10 16))
(.branch 436
(.leaf (.b 10 17))
(.leaf (.b 10 18))))))
(.branch 442
(.branch 439
(.branch 438
(.leaf (.b 10 19))
(.leaf (.b 10 20)))
(.branch 440
(.leaf (.b 10 21))
(.branch 441
(.leaf (.b 11 11))
(.leaf (.b 11 12)))))
(.branch 445
(.branch 443
(.leaf (.b 11 13))
(.branch 444
(.leaf (.b 11 14))
(.leaf (.b 11 15))))
(.branch 446
(.leaf (.b 11 16))
(.branch 447
(.leaf (.b 11 17))
(.leaf (.b 11 18)))))))
(.branch 459
(.branch 453
(.branch 450
(.branch 449
(.leaf (.b 11 19))
(.leaf (.b 11 20)))
(.branch 451
(.leaf (.b 11 21))
(.branch 452
(.leaf (.b 12 12))
(.leaf (.b 12 13)))))
(.branch 456
(.branch 454
(.leaf (.b 12 14))
(.branch 455
(.leaf (.b 12 15))
(.leaf (.b 12 16))))
(.branch 457
(.leaf (.b 12 17))
(.branch 458
(.leaf (.b 12 18))
(.leaf (.b 12 19))))))
(.branch 464
(.branch 461
(.branch 460
(.leaf (.b 12 20))
(.leaf (.b 12 21)))
(.branch 462
(.leaf (.b 13 13))
(.branch 463
(.leaf (.b 13 14))
(.leaf (.b 13 15)))))
(.branch 467
(.branch 465
(.leaf (.b 13 16))
(.branch 466
(.leaf (.b 13 17))
(.leaf (.b 13 18))))
(.branch 468
(.leaf (.b 13 19))
(.branch 469
(.leaf (.b 13 20))
(.leaf (.b 13 21))))))))
(.branch 491
(.branch 480
(.branch 475
(.branch 472
(.branch 471
(.leaf (.b 14 14))
(.leaf (.b 14 15)))
(.branch 473
(.leaf (.b 14 16))
(.branch 474
(.leaf (.b 14 17))
(.leaf (.b 14 18)))))
(.branch 477
(.branch 476
(.leaf (.b 14 19))
(.leaf (.b 14 20)))
(.branch 478
(.leaf (.b 14 21))
(.branch 479
(.leaf (.b 15 15))
(.leaf (.b 15 16))))))
(.branch 485
(.branch 482
(.branch 481
(.leaf (.b 15 17))
(.leaf (.b 15 18)))
(.branch 483
(.leaf (.b 15 19))
(.branch 484
(.leaf (.b 15 20))
(.leaf (.b 15 21)))))
(.branch 488
(.branch 486
(.leaf (.b 16 16))
(.branch 487
(.leaf (.b 16 17))
(.leaf (.b 16 18))))
(.branch 489
(.leaf (.b 16 19))
(.branch 490
(.leaf (.b 16 20))
(.leaf (.b 16 21)))))))
(.branch 502
(.branch 496
(.branch 493
(.branch 492
(.leaf (.b 17 17))
(.leaf (.b 17 18)))
(.branch 494
(.leaf (.b 17 19))
(.branch 495
(.leaf (.b 17 20))
(.leaf (.b 17 21)))))
(.branch 499
(.branch 497
(.leaf (.b 18 18))
(.branch 498
(.leaf (.b 18 19))
(.leaf (.b 18 20))))
(.branch 500
(.leaf (.b 18 21))
(.branch 501
(.leaf (.b 19 19))
(.leaf (.b 19 20))))))
(.branch 507
(.branch 504
(.branch 503
(.leaf (.b 19 21))
(.leaf (.b 20 20)))
(.branch 505
(.leaf (.b 20 21))
(.branch 506
(.leaf (.b 21 21))
(.leaf (.m 0 0)))))
(.branch 510
(.branch 508
(.leaf (.m 0 1))
(.branch 509
(.leaf (.m 1 1))
(.leaf (.m 0 2))))
(.branch 511
(.leaf (.m 1 2))
(.branch 512
(.leaf (.m 2 2))
(.leaf (.m 0 3))))))))))
(.branch 598
(.branch 555
(.branch 534
(.branch 523
(.branch 518
(.branch 515
(.branch 514
(.leaf (.m 1 3))
(.leaf (.m 2 3)))
(.branch 516
(.leaf (.m 3 3))
(.branch 517
(.leaf (.m 0 4))
(.leaf (.m 1 4)))))
(.branch 520
(.branch 519
(.leaf (.m 2 4))
(.leaf (.m 3 4)))
(.branch 521
(.leaf (.m 4 4))
(.branch 522
(.leaf (.m 0 5))
(.leaf (.m 1 5))))))
(.branch 528
(.branch 525
(.branch 524
(.leaf (.m 2 5))
(.leaf (.m 3 5)))
(.branch 526
(.leaf (.m 4 5))
(.branch 527
(.leaf (.m 5 5))
(.leaf (.m 0 6)))))
(.branch 531
(.branch 529
(.leaf (.m 1 6))
(.branch 530
(.leaf (.m 2 6))
(.leaf (.m 3 6))))
(.branch 532
(.leaf (.m 4 6))
(.branch 533
(.leaf (.m 5 6))
(.leaf (.m 6 6)))))))
(.branch 544
(.branch 539
(.branch 536
(.branch 535
(.leaf (.m 0 7))
(.leaf (.m 1 7)))
(.branch 537
(.leaf (.m 2 7))
(.branch 538
(.leaf (.m 3 7))
(.leaf (.m 4 7)))))
(.branch 541
(.branch 540
(.leaf (.m 5 7))
(.leaf (.m 6 7)))
(.branch 542
(.leaf (.m 7 7))
(.branch 543
(.leaf (.m 0 8))
(.leaf (.m 1 8))))))
(.branch 549
(.branch 546
(.branch 545
(.leaf (.m 2 8))
(.leaf (.m 3 8)))
(.branch 547
(.leaf (.m 4 8))
(.branch 548
(.leaf (.m 5 8))
(.leaf (.m 6 8)))))
(.branch 552
(.branch 550
(.leaf (.m 7 8))
(.branch 551
(.leaf (.m 8 8))
(.leaf (.m 0 9))))
(.branch 553
(.leaf (.m 1 9))
(.branch 554
(.leaf (.m 2 9))
(.leaf (.m 3 9))))))))
(.branch 576
(.branch 565
(.branch 560
(.branch 557
(.branch 556
(.leaf (.m 4 9))
(.leaf (.m 5 9)))
(.branch 558
(.leaf (.m 6 9))
(.branch 559
(.leaf (.m 7 9))
(.leaf (.m 8 9)))))
(.branch 562
(.branch 561
(.leaf (.m 9 9))
(.leaf (.m 0 10)))
(.branch 563
(.leaf (.m 1 10))
(.branch 564
(.leaf (.m 2 10))
(.leaf (.m 3 10))))))
(.branch 570
(.branch 567
(.branch 566
(.leaf (.m 4 10))
(.leaf (.m 5 10)))
(.branch 568
(.leaf (.m 6 10))
(.branch 569
(.leaf (.m 7 10))
(.leaf (.m 8 10)))))
(.branch 573
(.branch 571
(.leaf (.m 9 10))
(.branch 572
(.leaf (.m 10 10))
(.leaf (.m 0 11))))
(.branch 574
(.leaf (.m 1 11))
(.branch 575
(.leaf (.m 2 11))
(.leaf (.m 3 11)))))))
(.branch 587
(.branch 581
(.branch 578
(.branch 577
(.leaf (.m 4 11))
(.leaf (.m 5 11)))
(.branch 579
(.leaf (.m 6 11))
(.branch 580
(.leaf (.m 7 11))
(.leaf (.m 8 11)))))
(.branch 584
(.branch 582
(.leaf (.m 9 11))
(.branch 583
(.leaf (.m 10 11))
(.leaf (.m 11 11))))
(.branch 585
(.leaf (.m 0 12))
(.branch 586
(.leaf (.m 1 12))
(.leaf (.m 2 12))))))
(.branch 592
(.branch 589
(.branch 588
(.leaf (.m 3 12))
(.leaf (.m 4 12)))
(.branch 590
(.leaf (.m 5 12))
(.branch 591
(.leaf (.m 6 12))
(.leaf (.m 7 12)))))
(.branch 595
(.branch 593
(.leaf (.m 8 12))
(.branch 594
(.leaf (.m 9 12))
(.leaf (.m 10 12))))
(.branch 596
(.leaf (.m 11 12))
(.branch 597
(.leaf (.m 12 12))
(.leaf (.m 0 13)))))))))
(.branch 641
(.branch 619
(.branch 608
(.branch 603
(.branch 600
(.branch 599
(.leaf (.m 1 13))
(.leaf (.m 2 13)))
(.branch 601
(.leaf (.m 3 13))
(.branch 602
(.leaf (.m 4 13))
(.leaf (.m 5 13)))))
(.branch 605
(.branch 604
(.leaf (.m 6 13))
(.leaf (.m 7 13)))
(.branch 606
(.leaf (.m 8 13))
(.branch 607
(.leaf (.m 9 13))
(.leaf (.m 10 13))))))
(.branch 613
(.branch 610
(.branch 609
(.leaf (.m 11 13))
(.leaf (.m 12 13)))
(.branch 611
(.leaf (.m 13 13))
(.branch 612
(.leaf (.m 0 14))
(.leaf (.m 1 14)))))
(.branch 616
(.branch 614
(.leaf (.m 2 14))
(.branch 615
(.leaf (.m 3 14))
(.leaf (.m 4 14))))
(.branch 617
(.leaf (.m 5 14))
(.branch 618
(.leaf (.m 6 14))
(.leaf (.m 7 14)))))))
(.branch 630
(.branch 624
(.branch 621
(.branch 620
(.leaf (.m 8 14))
(.leaf (.m 9 14)))
(.branch 622
(.leaf (.m 10 14))
(.branch 623
(.leaf (.m 11 14))
(.leaf (.m 12 14)))))
(.branch 627
(.branch 625
(.leaf (.m 13 14))
(.branch 626
(.leaf (.m 14 14))
(.leaf (.m 0 15))))
(.branch 628
(.leaf (.m 1 15))
(.branch 629
(.leaf (.m 2 15))
(.leaf (.m 3 15))))))
(.branch 635
(.branch 632
(.branch 631
(.leaf (.m 4 15))
(.leaf (.m 5 15)))
(.branch 633
(.leaf (.m 6 15))
(.branch 634
(.leaf (.m 7 15))
(.leaf (.m 8 15)))))
(.branch 638
(.branch 636
(.leaf (.m 9 15))
(.branch 637
(.leaf (.m 10 15))
(.leaf (.m 11 15))))
(.branch 639
(.leaf (.m 12 15))
(.branch 640
(.leaf (.m 13 15))
(.leaf (.m 14 15))))))))
(.branch 662
(.branch 651
(.branch 646
(.branch 643
(.branch 642
(.leaf (.m 15 15))
(.leaf (.m 0 16)))
(.branch 644
(.leaf (.m 1 16))
(.branch 645
(.leaf (.m 2 16))
(.leaf (.m 3 16)))))
(.branch 648
(.branch 647
(.leaf (.m 4 16))
(.leaf (.m 5 16)))
(.branch 649
(.leaf (.m 6 16))
(.branch 650
(.leaf (.m 7 16))
(.leaf (.m 8 16))))))
(.branch 656
(.branch 653
(.branch 652
(.leaf (.m 9 16))
(.leaf (.m 10 16)))
(.branch 654
(.leaf (.m 11 16))
(.branch 655
(.leaf (.m 12 16))
(.leaf (.m 13 16)))))
(.branch 659
(.branch 657
(.leaf (.m 14 16))
(.branch 658
(.leaf (.m 15 16))
(.leaf (.m 16 16))))
(.branch 660
(.leaf (.m 0 17))
(.branch 661
(.leaf (.m 1 17))
(.leaf (.m 2 17)))))))
(.branch 673
(.branch 667
(.branch 664
(.branch 663
(.leaf (.m 3 17))
(.leaf (.m 4 17)))
(.branch 665
(.leaf (.m 5 17))
(.branch 666
(.leaf (.m 6 17))
(.leaf (.m 7 17)))))
(.branch 670
(.branch 668
(.leaf (.m 8 17))
(.branch 669
(.leaf (.m 9 17))
(.leaf (.m 10 17))))
(.branch 671
(.leaf (.m 11 17))
(.branch 672
(.leaf (.m 12 17))
(.leaf (.m 13 17))))))
(.branch 678
(.branch 675
(.branch 674
(.leaf (.m 14 17))
(.leaf (.m 15 17)))
(.branch 676
(.leaf (.m 16 17))
(.branch 677
(.leaf (.m 17 17))
(.leaf (.m 0 18)))))
(.branch 681
(.branch 679
(.leaf (.m 1 18))
(.branch 680
(.leaf (.m 2 18))
(.leaf (.m 3 18))))
(.branch 682
(.leaf (.m 4 18))
(.branch 683
(.leaf (.m 5 18))
(.leaf (.m 6 18))))))))))))
(.branch 1026
(.branch 855
(.branch 769
(.branch 726
(.branch 705
(.branch 694
(.branch 689
(.branch 686
(.branch 685
(.leaf (.m 7 18))
(.leaf (.m 8 18)))
(.branch 687
(.leaf (.m 9 18))
(.branch 688
(.leaf (.m 10 18))
(.leaf (.m 11 18)))))
(.branch 691
(.branch 690
(.leaf (.m 12 18))
(.leaf (.m 13 18)))
(.branch 692
(.leaf (.m 14 18))
(.branch 693
(.leaf (.m 15 18))
(.leaf (.m 16 18))))))
(.branch 699
(.branch 696
(.branch 695
(.leaf (.m 17 18))
(.leaf (.m 18 18)))
(.branch 697
(.leaf (.m 0 19))
(.branch 698
(.leaf (.m 1 19))
(.leaf (.m 2 19)))))
(.branch 702
(.branch 700
(.leaf (.m 3 19))
(.branch 701
(.leaf (.m 4 19))
(.leaf (.m 5 19))))
(.branch 703
(.leaf (.m 6 19))
(.branch 704
(.leaf (.m 7 19))
(.leaf (.m 8 19)))))))
(.branch 715
(.branch 710
(.branch 707
(.branch 706
(.leaf (.m 9 19))
(.leaf (.m 10 19)))
(.branch 708
(.leaf (.m 11 19))
(.branch 709
(.leaf (.m 12 19))
(.leaf (.m 13 19)))))
(.branch 712
(.branch 711
(.leaf (.m 14 19))
(.leaf (.m 15 19)))
(.branch 713
(.leaf (.m 16 19))
(.branch 714
(.leaf (.m 17 19))
(.leaf (.m 18 19))))))
(.branch 720
(.branch 717
(.branch 716
(.leaf (.m 19 19))
(.leaf (.m 0 20)))
(.branch 718
(.leaf (.m 1 20))
(.branch 719
(.leaf (.m 2 20))
(.leaf (.m 3 20)))))
(.branch 723
(.branch 721
(.leaf (.m 4 20))
(.branch 722
(.leaf (.m 5 20))
(.leaf (.m 6 20))))
(.branch 724
(.leaf (.m 7 20))
(.branch 725
(.leaf (.m 8 20))
(.leaf (.m 9 20))))))))
(.branch 747
(.branch 736
(.branch 731
(.branch 728
(.branch 727
(.leaf (.m 10 20))
(.leaf (.m 11 20)))
(.branch 729
(.leaf (.m 12 20))
(.branch 730
(.leaf (.m 13 20))
(.leaf (.m 14 20)))))
(.branch 733
(.branch 732
(.leaf (.m 15 20))
(.leaf (.m 16 20)))
(.branch 734
(.leaf (.m 17 20))
(.branch 735
(.leaf (.m 18 20))
(.leaf (.m 19 20))))))
(.branch 741
(.branch 738
(.branch 737
(.leaf (.m 20 20))
(.leaf (.p 0 1)))
(.branch 739
(.leaf (.p 0 2))
(.branch 740
(.leaf (.p 0 3))
(.leaf (.p 0 4)))))
(.branch 744
(.branch 742
(.leaf (.p 0 5))
(.branch 743
(.leaf (.p 0 6))
(.leaf (.p 0 7))))
(.branch 745
(.leaf (.p 0 8))
(.branch 746
(.leaf (.p 0 9))
(.leaf (.p 0 10)))))))
(.branch 758
(.branch 752
(.branch 749
(.branch 748
(.leaf (.p 0 11))
(.leaf (.p 0 12)))
(.branch 750
(.leaf (.p 0 13))
(.branch 751
(.leaf (.p 0 14))
(.leaf (.p 0 15)))))
(.branch 755
(.branch 753
(.leaf (.p 0 16))
(.branch 754
(.leaf (.p 0 17))
(.leaf (.p 0 18))))
(.branch 756
(.leaf (.p 0 19))
(.branch 757
(.leaf (.p 0 20))
(.leaf (.p 0 21))))))
(.branch 763
(.branch 760
(.branch 759
(.leaf (.p 1 2))
(.leaf (.p 1 3)))
(.branch 761
(.leaf (.p 1 4))
(.branch 762
(.leaf (.p 1 5))
(.leaf (.p 1 6)))))
(.branch 766
(.branch 764
(.leaf (.p 1 7))
(.branch 765
(.leaf (.p 1 8))
(.leaf (.p 1 9))))
(.branch 767
(.leaf (.p 1 10))
(.branch 768
(.leaf (.p 1 11))
(.leaf (.p 1 12)))))))))
(.branch 812
(.branch 790
(.branch 779
(.branch 774
(.branch 771
(.branch 770
(.leaf (.p 1 13))
(.leaf (.p 1 14)))
(.branch 772
(.leaf (.p 1 15))
(.branch 773
(.leaf (.p 1 16))
(.leaf (.p 1 17)))))
(.branch 776
(.branch 775
(.leaf (.p 1 18))
(.leaf (.p 1 19)))
(.branch 777
(.leaf (.p 1 20))
(.branch 778
(.leaf (.p 1 21))
(.leaf (.p 2 3))))))
(.branch 784
(.branch 781
(.branch 780
(.leaf (.p 2 4))
(.leaf (.p 2 5)))
(.branch 782
(.leaf (.p 2 6))
(.branch 783
(.leaf (.p 2 7))
(.leaf (.p 2 8)))))
(.branch 787
(.branch 785
(.leaf (.p 2 9))
(.branch 786
(.leaf (.p 2 10))
(.leaf (.p 2 11))))
(.branch 788
(.leaf (.p 2 12))
(.branch 789
(.leaf (.p 2 13))
(.leaf (.p 2 14)))))))
(.branch 801
(.branch 795
(.branch 792
(.branch 791
(.leaf (.p 2 15))
(.leaf (.p 2 16)))
(.branch 793
(.leaf (.p 2 17))
(.branch 794
(.leaf (.p 2 18))
(.leaf (.p 2 19)))))
(.branch 798
(.branch 796
(.leaf (.p 2 20))
(.branch 797
(.leaf (.p 2 21))
(.leaf (.p 3 4))))
(.branch 799
(.leaf (.p 3 5))
(.branch 800
(.leaf (.p 3 6))
(.leaf (.p 3 7))))))
(.branch 806
(.branch 803
(.branch 802
(.leaf (.p 3 8))
(.leaf (.p 3 9)))
(.branch 804
(.leaf (.p 3 10))
(.branch 805
(.leaf (.p 3 11))
(.leaf (.p 3 12)))))
(.branch 809
(.branch 807
(.leaf (.p 3 13))
(.branch 808
(.leaf (.p 3 14))
(.leaf (.p 3 15))))
(.branch 810
(.leaf (.p 3 16))
(.branch 811
(.leaf (.p 3 17))
(.leaf (.p 3 18))))))))
(.branch 833
(.branch 822
(.branch 817
(.branch 814
(.branch 813
(.leaf (.p 3 19))
(.leaf (.p 3 20)))
(.branch 815
(.leaf (.p 3 21))
(.branch 816
(.leaf (.p 4 5))
(.leaf (.p 4 6)))))
(.branch 819
(.branch 818
(.leaf (.p 4 7))
(.leaf (.p 4 8)))
(.branch 820
(.leaf (.p 4 9))
(.branch 821
(.leaf (.p 4 10))
(.leaf (.p 4 11))))))
(.branch 827
(.branch 824
(.branch 823
(.leaf (.p 4 12))
(.leaf (.p 4 13)))
(.branch 825
(.leaf (.p 4 14))
(.branch 826
(.leaf (.p 4 15))
(.leaf (.p 4 16)))))
(.branch 830
(.branch 828
(.leaf (.p 4 17))
(.branch 829
(.leaf (.p 4 18))
(.leaf (.p 4 19))))
(.branch 831
(.leaf (.p 4 20))
(.branch 832
(.leaf (.p 4 21))
(.leaf (.p 5 6)))))))
(.branch 844
(.branch 838
(.branch 835
(.branch 834
(.leaf (.p 5 7))
(.leaf (.p 5 8)))
(.branch 836
(.leaf (.p 5 9))
(.branch 837
(.leaf (.p 5 10))
(.leaf (.p 5 11)))))
(.branch 841
(.branch 839
(.leaf (.p 5 12))
(.branch 840
(.leaf (.p 5 13))
(.leaf (.p 5 14))))
(.branch 842
(.leaf (.p 5 15))
(.branch 843
(.leaf (.p 5 16))
(.leaf (.p 5 17))))))
(.branch 849
(.branch 846
(.branch 845
(.leaf (.p 5 18))
(.leaf (.p 5 19)))
(.branch 847
(.leaf (.p 5 20))
(.branch 848
(.leaf (.p 5 21))
(.leaf (.p 6 7)))))
(.branch 852
(.branch 850
(.leaf (.p 6 8))
(.branch 851
(.leaf (.p 6 9))
(.leaf (.p 6 10))))
(.branch 853
(.leaf (.p 6 11))
(.branch 854
(.leaf (.p 6 12))
(.leaf (.p 6 13))))))))))
(.branch 940
(.branch 897
(.branch 876
(.branch 865
(.branch 860
(.branch 857
(.branch 856
(.leaf (.p 6 14))
(.leaf (.p 6 15)))
(.branch 858
(.leaf (.p 6 16))
(.branch 859
(.leaf (.p 6 17))
(.leaf (.p 6 18)))))
(.branch 862
(.branch 861
(.leaf (.p 6 19))
(.leaf (.p 6 20)))
(.branch 863
(.leaf (.p 6 21))
(.branch 864
(.leaf (.p 7 8))
(.leaf (.p 7 9))))))
(.branch 870
(.branch 867
(.branch 866
(.leaf (.p 7 10))
(.leaf (.p 7 11)))
(.branch 868
(.leaf (.p 7 12))
(.branch 869
(.leaf (.p 7 13))
(.leaf (.p 7 14)))))
(.branch 873
(.branch 871
(.leaf (.p 7 15))
(.branch 872
(.leaf (.p 7 16))
(.leaf (.p 7 17))))
(.branch 874
(.leaf (.p 7 18))
(.branch 875
(.leaf (.p 7 19))
(.leaf (.p 7 20)))))))
(.branch 886
(.branch 881
(.branch 878
(.branch 877
(.leaf (.p 7 21))
(.leaf (.p 8 9)))
(.branch 879
(.leaf (.p 8 10))
(.branch 880
(.leaf (.p 8 11))
(.leaf (.p 8 12)))))
(.branch 883
(.branch 882
(.leaf (.p 8 13))
(.leaf (.p 8 14)))
(.branch 884
(.leaf (.p 8 15))
(.branch 885
(.leaf (.p 8 16))
(.leaf (.p 8 17))))))
(.branch 891
(.branch 888
(.branch 887
(.leaf (.p 8 18))
(.leaf (.p 8 19)))
(.branch 889
(.leaf (.p 8 20))
(.branch 890
(.leaf (.p 8 21))
(.leaf (.p 9 10)))))
(.branch 894
(.branch 892
(.leaf (.p 9 11))
(.branch 893
(.leaf (.p 9 12))
(.leaf (.p 9 13))))
(.branch 895
(.leaf (.p 9 14))
(.branch 896
(.leaf (.p 9 15))
(.leaf (.p 9 16))))))))
(.branch 918
(.branch 907
(.branch 902
(.branch 899
(.branch 898
(.leaf (.p 9 17))
(.leaf (.p 9 18)))
(.branch 900
(.leaf (.p 9 19))
(.branch 901
(.leaf (.p 9 20))
(.leaf (.p 9 21)))))
(.branch 904
(.branch 903
(.leaf (.p 10 11))
(.leaf (.p 10 12)))
(.branch 905
(.leaf (.p 10 13))
(.branch 906
(.leaf (.p 10 14))
(.leaf (.p 10 15))))))
(.branch 912
(.branch 909
(.branch 908
(.leaf (.p 10 16))
(.leaf (.p 10 17)))
(.branch 910
(.leaf (.p 10 18))
(.branch 911
(.leaf (.p 10 19))
(.leaf (.p 10 20)))))
(.branch 915
(.branch 913
(.leaf (.p 10 21))
(.branch 914
(.leaf (.p 11 12))
(.leaf (.p 11 13))))
(.branch 916
(.leaf (.p 11 14))
(.branch 917
(.leaf (.p 11 15))
(.leaf (.p 11 16)))))))
(.branch 929
(.branch 923
(.branch 920
(.branch 919
(.leaf (.p 11 17))
(.leaf (.p 11 18)))
(.branch 921
(.leaf (.p 11 19))
(.branch 922
(.leaf (.p 11 20))
(.leaf (.p 11 21)))))
(.branch 926
(.branch 924
(.leaf (.p 12 13))
(.branch 925
(.leaf (.p 12 14))
(.leaf (.p 12 15))))
(.branch 927
(.leaf (.p 12 16))
(.branch 928
(.leaf (.p 12 17))
(.leaf (.p 12 18))))))
(.branch 934
(.branch 931
(.branch 930
(.leaf (.p 12 19))
(.leaf (.p 12 20)))
(.branch 932
(.leaf (.p 12 21))
(.branch 933
(.leaf (.p 13 14))
(.leaf (.p 13 15)))))
(.branch 937
(.branch 935
(.leaf (.p 13 16))
(.branch 936
(.leaf (.p 13 17))
(.leaf (.p 13 18))))
(.branch 938
(.leaf (.p 13 19))
(.branch 939
(.leaf (.p 13 20))
(.leaf (.p 13 21)))))))))
(.branch 983
(.branch 961
(.branch 950
(.branch 945
(.branch 942
(.branch 941
(.leaf (.p 14 15))
(.leaf (.p 14 16)))
(.branch 943
(.leaf (.p 14 17))
(.branch 944
(.leaf (.p 14 18))
(.leaf (.p 14 19)))))
(.branch 947
(.branch 946
(.leaf (.p 14 20))
(.leaf (.p 14 21)))
(.branch 948
(.leaf (.p 15 16))
(.branch 949
(.leaf (.p 15 17))
(.leaf (.p 15 18))))))
(.branch 955
(.branch 952
(.branch 951
(.leaf (.p 15 19))
(.leaf (.p 15 20)))
(.branch 953
(.leaf (.p 15 21))
(.branch 954
(.leaf (.p 16 17))
(.leaf (.p 16 18)))))
(.branch 958
(.branch 956
(.leaf (.p 16 19))
(.branch 957
(.leaf (.p 16 20))
(.leaf (.p 16 21))))
(.branch 959
(.leaf (.p 17 18))
(.branch 960
(.leaf (.p 17 19))
(.leaf (.p 17 20)))))))
(.branch 972
(.branch 966
(.branch 963
(.branch 962
(.leaf (.p 17 21))
(.leaf (.p 18 19)))
(.branch 964
(.leaf (.p 18 20))
(.branch 965
(.leaf (.p 18 21))
(.leaf (.p 19 20)))))
(.branch 969
(.branch 967
(.leaf (.p 19 21))
(.branch 968
(.leaf (.p 20 21))
(.leaf (.d 0 0 1))))
(.branch 970
(.leaf (.d 0 0 2))
(.branch 971
(.leaf (.d 0 0 3))
(.leaf (.d 0 0 4))))))
(.branch 977
(.branch 974
(.branch 973
(.leaf (.d 0 0 5))
(.leaf (.d 0 0 6)))
(.branch 975
(.leaf (.d 0 0 7))
(.branch 976
(.leaf (.d 0 0 8))
(.leaf (.d 0 0 9)))))
(.branch 980
(.branch 978
(.leaf (.d 0 0 10))
(.branch 979
(.leaf (.d 0 0 11))
(.leaf (.d 0 0 12))))
(.branch 981
(.leaf (.d 0 0 13))
(.branch 982
(.leaf (.d 0 0 14))
(.leaf (.d 0 0 15))))))))
(.branch 1004
(.branch 993
(.branch 988
(.branch 985
(.branch 984
(.leaf (.d 0 0 16))
(.leaf (.d 0 0 17)))
(.branch 986
(.leaf (.d 0 0 18))
(.branch 987
(.leaf (.d 0 0 19))
(.leaf (.d 0 0 20)))))
(.branch 990
(.branch 989
(.leaf (.d 0 0 21))
(.leaf (.d 0 1 2)))
(.branch 991
(.leaf (.d 0 1 3))
(.branch 992
(.leaf (.d 0 1 4))
(.leaf (.d 0 1 5))))))
(.branch 998
(.branch 995
(.branch 994
(.leaf (.d 0 1 6))
(.leaf (.d 0 1 7)))
(.branch 996
(.leaf (.d 0 1 8))
(.branch 997
(.leaf (.d 0 1 9))
(.leaf (.d 0 1 10)))))
(.branch 1001
(.branch 999
(.leaf (.d 0 1 11))
(.branch 1000
(.leaf (.d 0 1 12))
(.leaf (.d 0 1 13))))
(.branch 1002
(.leaf (.d 0 1 14))
(.branch 1003
(.leaf (.d 0 1 15))
(.leaf (.d 0 1 16)))))))
(.branch 1015
(.branch 1009
(.branch 1006
(.branch 1005
(.leaf (.d 0 1 17))
(.leaf (.d 0 1 18)))
(.branch 1007
(.leaf (.d 0 1 19))
(.branch 1008
(.leaf (.d 0 1 20))
(.leaf (.d 0 1 21)))))
(.branch 1012
(.branch 1010
(.leaf (.d 1 1 2))
(.branch 1011
(.leaf (.d 1 1 3))
(.leaf (.d 1 1 4))))
(.branch 1013
(.leaf (.d 1 1 5))
(.branch 1014
(.leaf (.d 1 1 6))
(.leaf (.d 1 1 7))))))
(.branch 1020
(.branch 1017
(.branch 1016
(.leaf (.d 1 1 8))
(.leaf (.d 1 1 9)))
(.branch 1018
(.leaf (.d 1 1 10))
(.branch 1019
(.leaf (.d 1 1 11))
(.leaf (.d 1 1 12)))))
(.branch 1023
(.branch 1021
(.leaf (.d 1 1 13))
(.branch 1022
(.leaf (.d 1 1 14))
(.leaf (.d 1 1 15))))
(.branch 1024
(.leaf (.d 1 1 16))
(.branch 1025
(.leaf (.d 1 1 17))
(.leaf (.d 1 1 18)))))))))))
(.branch 1197
(.branch 1111
(.branch 1068
(.branch 1047
(.branch 1036
(.branch 1031
(.branch 1028
(.branch 1027
(.leaf (.d 1 1 19))
(.leaf (.d 1 1 20)))
(.branch 1029
(.leaf (.d 1 1 21))
(.branch 1030
(.leaf (.d 0 2 3))
(.leaf (.d 0 2 4)))))
(.branch 1033
(.branch 1032
(.leaf (.d 0 2 5))
(.leaf (.d 0 2 6)))
(.branch 1034
(.leaf (.d 0 2 7))
(.branch 1035
(.leaf (.d 0 2 8))
(.leaf (.d 0 2 9))))))
(.branch 1041
(.branch 1038
(.branch 1037
(.leaf (.d 0 2 10))
(.leaf (.d 0 2 11)))
(.branch 1039
(.leaf (.d 0 2 12))
(.branch 1040
(.leaf (.d 0 2 13))
(.leaf (.d 0 2 14)))))
(.branch 1044
(.branch 1042
(.leaf (.d 0 2 15))
(.branch 1043
(.leaf (.d 0 2 16))
(.leaf (.d 0 2 17))))
(.branch 1045
(.leaf (.d 0 2 18))
(.branch 1046
(.leaf (.d 0 2 19))
(.leaf (.d 0 2 20)))))))
(.branch 1057
(.branch 1052
(.branch 1049
(.branch 1048
(.leaf (.d 0 2 21))
(.leaf (.d 1 2 3)))
(.branch 1050
(.leaf (.d 1 2 4))
(.branch 1051
(.leaf (.d 1 2 5))
(.leaf (.d 1 2 6)))))
(.branch 1054
(.branch 1053
(.leaf (.d 1 2 7))
(.leaf (.d 1 2 8)))
(.branch 1055
(.leaf (.d 1 2 9))
(.branch 1056
(.leaf (.d 1 2 10))
(.leaf (.d 1 2 11))))))
(.branch 1062
(.branch 1059
(.branch 1058
(.leaf (.d 1 2 12))
(.leaf (.d 1 2 13)))
(.branch 1060
(.leaf (.d 1 2 14))
(.branch 1061
(.leaf (.d 1 2 15))
(.leaf (.d 1 2 16)))))
(.branch 1065
(.branch 1063
(.leaf (.d 1 2 17))
(.branch 1064
(.leaf (.d 1 2 18))
(.leaf (.d 1 2 19))))
(.branch 1066
(.leaf (.d 1 2 20))
(.branch 1067
(.leaf (.d 1 2 21))
(.leaf (.d 2 2 3))))))))
(.branch 1089
(.branch 1078
(.branch 1073
(.branch 1070
(.branch 1069
(.leaf (.d 2 2 4))
(.leaf (.d 2 2 5)))
(.branch 1071
(.leaf (.d 2 2 6))
(.branch 1072
(.leaf (.d 2 2 7))
(.leaf (.d 2 2 8)))))
(.branch 1075
(.branch 1074
(.leaf (.d 2 2 9))
(.leaf (.d 2 2 10)))
(.branch 1076
(.leaf (.d 2 2 11))
(.branch 1077
(.leaf (.d 2 2 12))
(.leaf (.d 2 2 13))))))
(.branch 1083
(.branch 1080
(.branch 1079
(.leaf (.d 2 2 14))
(.leaf (.d 2 2 15)))
(.branch 1081
(.leaf (.d 2 2 16))
(.branch 1082
(.leaf (.d 2 2 17))
(.leaf (.d 2 2 18)))))
(.branch 1086
(.branch 1084
(.leaf (.d 2 2 19))
(.branch 1085
(.leaf (.d 2 2 20))
(.leaf (.d 2 2 21))))
(.branch 1087
(.leaf (.d 0 3 4))
(.branch 1088
(.leaf (.d 0 3 5))
(.leaf (.d 0 3 6)))))))
(.branch 1100
(.branch 1094
(.branch 1091
(.branch 1090
(.leaf (.d 0 3 7))
(.leaf (.d 0 3 8)))
(.branch 1092
(.leaf (.d 0 3 9))
(.branch 1093
(.leaf (.d 0 3 10))
(.leaf (.d 0 3 11)))))
(.branch 1097
(.branch 1095
(.leaf (.d 0 3 12))
(.branch 1096
(.leaf (.d 0 3 13))
(.leaf (.d 0 3 14))))
(.branch 1098
(.leaf (.d 0 3 15))
(.branch 1099
(.leaf (.d 0 3 16))
(.leaf (.d 0 3 17))))))
(.branch 1105
(.branch 1102
(.branch 1101
(.leaf (.d 0 3 18))
(.leaf (.d 0 3 19)))
(.branch 1103
(.leaf (.d 0 3 20))
(.branch 1104
(.leaf (.d 0 3 21))
(.leaf (.d 1 3 4)))))
(.branch 1108
(.branch 1106
(.leaf (.d 1 3 5))
(.branch 1107
(.leaf (.d 1 3 6))
(.leaf (.d 1 3 7))))
(.branch 1109
(.leaf (.d 1 3 8))
(.branch 1110
(.leaf (.d 1 3 9))
(.leaf (.d 1 3 10)))))))))
(.branch 1154
(.branch 1132
(.branch 1121
(.branch 1116
(.branch 1113
(.branch 1112
(.leaf (.d 1 3 11))
(.leaf (.d 1 3 12)))
(.branch 1114
(.leaf (.d 1 3 13))
(.branch 1115
(.leaf (.d 1 3 14))
(.leaf (.d 1 3 15)))))
(.branch 1118
(.branch 1117
(.leaf (.d 1 3 16))
(.leaf (.d 1 3 17)))
(.branch 1119
(.leaf (.d 1 3 18))
(.branch 1120
(.leaf (.d 1 3 19))
(.leaf (.d 1 3 20))))))
(.branch 1126
(.branch 1123
(.branch 1122
(.leaf (.d 1 3 21))
(.leaf (.d 2 3 4)))
(.branch 1124
(.leaf (.d 2 3 5))
(.branch 1125
(.leaf (.d 2 3 6))
(.leaf (.d 2 3 7)))))
(.branch 1129
(.branch 1127
(.leaf (.d 2 3 8))
(.branch 1128
(.leaf (.d 2 3 9))
(.leaf (.d 2 3 10))))
(.branch 1130
(.leaf (.d 2 3 11))
(.branch 1131
(.leaf (.d 2 3 12))
(.leaf (.d 2 3 13)))))))
(.branch 1143
(.branch 1137
(.branch 1134
(.branch 1133
(.leaf (.d 2 3 14))
(.leaf (.d 2 3 15)))
(.branch 1135
(.leaf (.d 2 3 16))
(.branch 1136
(.leaf (.d 2 3 17))
(.leaf (.d 2 3 18)))))
(.branch 1140
(.branch 1138
(.leaf (.d 2 3 19))
(.branch 1139
(.leaf (.d 2 3 20))
(.leaf (.d 2 3 21))))
(.branch 1141
(.leaf (.d 3 3 4))
(.branch 1142
(.leaf (.d 3 3 5))
(.leaf (.d 3 3 6))))))
(.branch 1148
(.branch 1145
(.branch 1144
(.leaf (.d 3 3 7))
(.leaf (.d 3 3 8)))
(.branch 1146
(.leaf (.d 3 3 9))
(.branch 1147
(.leaf (.d 3 3 10))
(.leaf (.d 3 3 11)))))
(.branch 1151
(.branch 1149
(.leaf (.d 3 3 12))
(.branch 1150
(.leaf (.d 3 3 13))
(.leaf (.d 3 3 14))))
(.branch 1152
(.leaf (.d 3 3 15))
(.branch 1153
(.leaf (.d 3 3 16))
(.leaf (.d 3 3 17))))))))
(.branch 1175
(.branch 1164
(.branch 1159
(.branch 1156
(.branch 1155
(.leaf (.d 3 3 18))
(.leaf (.d 3 3 19)))
(.branch 1157
(.leaf (.d 3 3 20))
(.branch 1158
(.leaf (.d 3 3 21))
(.leaf (.d 0 4 5)))))
(.branch 1161
(.branch 1160
(.leaf (.d 0 4 6))
(.leaf (.d 0 4 7)))
(.branch 1162
(.leaf (.d 0 4 8))
(.branch 1163
(.leaf (.d 0 4 9))
(.leaf (.d 0 4 10))))))
(.branch 1169
(.branch 1166
(.branch 1165
(.leaf (.d 0 4 11))
(.leaf (.d 0 4 12)))
(.branch 1167
(.leaf (.d 0 4 13))
(.branch 1168
(.leaf (.d 0 4 14))
(.leaf (.d 0 4 15)))))
(.branch 1172
(.branch 1170
(.leaf (.d 0 4 16))
(.branch 1171
(.leaf (.d 0 4 17))
(.leaf (.d 0 4 18))))
(.branch 1173
(.leaf (.d 0 4 19))
(.branch 1174
(.leaf (.d 0 4 20))
(.leaf (.d 0 4 21)))))))
(.branch 1186
(.branch 1180
(.branch 1177
(.branch 1176
(.leaf (.d 1 4 5))
(.leaf (.d 1 4 6)))
(.branch 1178
(.leaf (.d 1 4 7))
(.branch 1179
(.leaf (.d 1 4 8))
(.leaf (.d 1 4 9)))))
(.branch 1183
(.branch 1181
(.leaf (.d 1 4 10))
(.branch 1182
(.leaf (.d 1 4 11))
(.leaf (.d 1 4 12))))
(.branch 1184
(.leaf (.d 1 4 13))
(.branch 1185
(.leaf (.d 1 4 14))
(.leaf (.d 1 4 15))))))
(.branch 1191
(.branch 1188
(.branch 1187
(.leaf (.d 1 4 16))
(.leaf (.d 1 4 17)))
(.branch 1189
(.leaf (.d 1 4 18))
(.branch 1190
(.leaf (.d 1 4 19))
(.leaf (.d 1 4 20)))))
(.branch 1194
(.branch 1192
(.leaf (.d 1 4 21))
(.branch 1193
(.leaf (.d 2 4 5))
(.leaf (.d 2 4 6))))
(.branch 1195
(.leaf (.d 2 4 7))
(.branch 1196
(.leaf (.d 2 4 8))
(.leaf (.d 2 4 9))))))))))
(.branch 1283
(.branch 1240
(.branch 1218
(.branch 1207
(.branch 1202
(.branch 1199
(.branch 1198
(.leaf (.d 2 4 10))
(.leaf (.d 2 4 11)))
(.branch 1200
(.leaf (.d 2 4 12))
(.branch 1201
(.leaf (.d 2 4 13))
(.leaf (.d 2 4 14)))))
(.branch 1204
(.branch 1203
(.leaf (.d 2 4 15))
(.leaf (.d 2 4 16)))
(.branch 1205
(.leaf (.d 2 4 17))
(.branch 1206
(.leaf (.d 2 4 18))
(.leaf (.d 2 4 19))))))
(.branch 1212
(.branch 1209
(.branch 1208
(.leaf (.d 2 4 20))
(.leaf (.d 2 4 21)))
(.branch 1210
(.leaf (.d 3 4 5))
(.branch 1211
(.leaf (.d 3 4 6))
(.leaf (.d 3 4 7)))))
(.branch 1215
(.branch 1213
(.leaf (.d 3 4 8))
(.branch 1214
(.leaf (.d 3 4 9))
(.leaf (.d 3 4 10))))
(.branch 1216
(.leaf (.d 3 4 11))
(.branch 1217
(.leaf (.d 3 4 12))
(.leaf (.d 3 4 13)))))))
(.branch 1229
(.branch 1223
(.branch 1220
(.branch 1219
(.leaf (.d 3 4 14))
(.leaf (.d 3 4 15)))
(.branch 1221
(.leaf (.d 3 4 16))
(.branch 1222
(.leaf (.d 3 4 17))
(.leaf (.d 3 4 18)))))
(.branch 1226
(.branch 1224
(.leaf (.d 3 4 19))
(.branch 1225
(.leaf (.d 3 4 20))
(.leaf (.d 3 4 21))))
(.branch 1227
(.leaf (.d 4 4 5))
(.branch 1228
(.leaf (.d 4 4 6))
(.leaf (.d 4 4 7))))))
(.branch 1234
(.branch 1231
(.branch 1230
(.leaf (.d 4 4 8))
(.leaf (.d 4 4 9)))
(.branch 1232
(.leaf (.d 4 4 10))
(.branch 1233
(.leaf (.d 4 4 11))
(.leaf (.d 4 4 12)))))
(.branch 1237
(.branch 1235
(.leaf (.d 4 4 13))
(.branch 1236
(.leaf (.d 4 4 14))
(.leaf (.d 4 4 15))))
(.branch 1238
(.leaf (.d 4 4 16))
(.branch 1239
(.leaf (.d 4 4 17))
(.leaf (.d 4 4 18))))))))
(.branch 1261
(.branch 1250
(.branch 1245
(.branch 1242
(.branch 1241
(.leaf (.d 4 4 19))
(.leaf (.d 4 4 20)))
(.branch 1243
(.leaf (.d 4 4 21))
(.branch 1244
(.leaf (.d 0 5 6))
(.leaf (.d 0 5 7)))))
(.branch 1247
(.branch 1246
(.leaf (.d 0 5 8))
(.leaf (.d 0 5 9)))
(.branch 1248
(.leaf (.d 0 5 10))
(.branch 1249
(.leaf (.d 0 5 11))
(.leaf (.d 0 5 12))))))
(.branch 1255
(.branch 1252
(.branch 1251
(.leaf (.d 0 5 13))
(.leaf (.d 0 5 14)))
(.branch 1253
(.leaf (.d 0 5 15))
(.branch 1254
(.leaf (.d 0 5 16))
(.leaf (.d 0 5 17)))))
(.branch 1258
(.branch 1256
(.leaf (.d 0 5 18))
(.branch 1257
(.leaf (.d 0 5 19))
(.leaf (.d 0 5 20))))
(.branch 1259
(.leaf (.d 0 5 21))
(.branch 1260
(.leaf (.d 1 5 6))
(.leaf (.d 1 5 7)))))))
(.branch 1272
(.branch 1266
(.branch 1263
(.branch 1262
(.leaf (.d 1 5 8))
(.leaf (.d 1 5 9)))
(.branch 1264
(.leaf (.d 1 5 10))
(.branch 1265
(.leaf (.d 1 5 11))
(.leaf (.d 1 5 12)))))
(.branch 1269
(.branch 1267
(.leaf (.d 1 5 13))
(.branch 1268
(.leaf (.d 1 5 14))
(.leaf (.d 1 5 15))))
(.branch 1270
(.leaf (.d 1 5 16))
(.branch 1271
(.leaf (.d 1 5 17))
(.leaf (.d 1 5 18))))))
(.branch 1277
(.branch 1274
(.branch 1273
(.leaf (.d 1 5 19))
(.leaf (.d 1 5 20)))
(.branch 1275
(.leaf (.d 1 5 21))
(.branch 1276
(.leaf (.d 2 5 6))
(.leaf (.d 2 5 7)))))
(.branch 1280
(.branch 1278
(.leaf (.d 2 5 8))
(.branch 1279
(.leaf (.d 2 5 9))
(.leaf (.d 2 5 10))))
(.branch 1281
(.leaf (.d 2 5 11))
(.branch 1282
(.leaf (.d 2 5 12))
(.leaf (.d 2 5 13)))))))))
(.branch 1326
(.branch 1304
(.branch 1293
(.branch 1288
(.branch 1285
(.branch 1284
(.leaf (.d 2 5 14))
(.leaf (.d 2 5 15)))
(.branch 1286
(.leaf (.d 2 5 16))
(.branch 1287
(.leaf (.d 2 5 17))
(.leaf (.d 2 5 18)))))
(.branch 1290
(.branch 1289
(.leaf (.d 2 5 19))
(.leaf (.d 2 5 20)))
(.branch 1291
(.leaf (.d 2 5 21))
(.branch 1292
(.leaf (.d 3 5 6))
(.leaf (.d 3 5 7))))))
(.branch 1298
(.branch 1295
(.branch 1294
(.leaf (.d 3 5 8))
(.leaf (.d 3 5 9)))
(.branch 1296
(.leaf (.d 3 5 10))
(.branch 1297
(.leaf (.d 3 5 11))
(.leaf (.d 3 5 12)))))
(.branch 1301
(.branch 1299
(.leaf (.d 3 5 13))
(.branch 1300
(.leaf (.d 3 5 14))
(.leaf (.d 3 5 15))))
(.branch 1302
(.leaf (.d 3 5 16))
(.branch 1303
(.leaf (.d 3 5 17))
(.leaf (.d 3 5 18)))))))
(.branch 1315
(.branch 1309
(.branch 1306
(.branch 1305
(.leaf (.d 3 5 19))
(.leaf (.d 3 5 20)))
(.branch 1307
(.leaf (.d 3 5 21))
(.branch 1308
(.leaf (.d 4 5 6))
(.leaf (.d 4 5 7)))))
(.branch 1312
(.branch 1310
(.leaf (.d 4 5 8))
(.branch 1311
(.leaf (.d 4 5 9))
(.leaf (.d 4 5 10))))
(.branch 1313
(.leaf (.d 4 5 11))
(.branch 1314
(.leaf (.d 4 5 12))
(.leaf (.d 4 5 13))))))
(.branch 1320
(.branch 1317
(.branch 1316
(.leaf (.d 4 5 14))
(.leaf (.d 4 5 15)))
(.branch 1318
(.leaf (.d 4 5 16))
(.branch 1319
(.leaf (.d 4 5 17))
(.leaf (.d 4 5 18)))))
(.branch 1323
(.branch 1321
(.leaf (.d 4 5 19))
(.branch 1322
(.leaf (.d 4 5 20))
(.leaf (.d 4 5 21))))
(.branch 1324
(.leaf (.d 5 5 6))
(.branch 1325
(.leaf (.d 5 5 7))
(.leaf (.d 5 5 8))))))))
(.branch 1347
(.branch 1336
(.branch 1331
(.branch 1328
(.branch 1327
(.leaf (.d 5 5 9))
(.leaf (.d 5 5 10)))
(.branch 1329
(.leaf (.d 5 5 11))
(.branch 1330
(.leaf (.d 5 5 12))
(.leaf (.d 5 5 13)))))
(.branch 1333
(.branch 1332
(.leaf (.d 5 5 14))
(.leaf (.d 5 5 15)))
(.branch 1334
(.leaf (.d 5 5 16))
(.branch 1335
(.leaf (.d 5 5 17))
(.leaf (.d 5 5 18))))))
(.branch 1341
(.branch 1338
(.branch 1337
(.leaf (.d 5 5 19))
(.leaf (.d 5 5 20)))
(.branch 1339
(.leaf (.d 5 5 21))
(.branch 1340
(.leaf (.d 0 6 7))
(.leaf (.d 0 6 8)))))
(.branch 1344
(.branch 1342
(.leaf (.d 0 6 9))
(.branch 1343
(.leaf (.d 0 6 10))
(.leaf (.d 0 6 11))))
(.branch 1345
(.leaf (.d 0 6 12))
(.branch 1346
(.leaf (.d 0 6 13))
(.leaf (.d 0 6 14)))))))
(.branch 1358
(.branch 1352
(.branch 1349
(.branch 1348
(.leaf (.d 0 6 15))
(.leaf (.d 0 6 16)))
(.branch 1350
(.leaf (.d 0 6 17))
(.branch 1351
(.leaf (.d 0 6 18))
(.leaf (.d 0 6 19)))))
(.branch 1355
(.branch 1353
(.leaf (.d 0 6 20))
(.branch 1354
(.leaf (.d 0 6 21))
(.leaf (.d 1 6 7))))
(.branch 1356
(.leaf (.d 1 6 8))
(.branch 1357
(.leaf (.d 1 6 9))
(.leaf (.d 1 6 10))))))
(.branch 1363
(.branch 1360
(.branch 1359
(.leaf (.d 1 6 11))
(.leaf (.d 1 6 12)))
(.branch 1361
(.leaf (.d 1 6 13))
(.branch 1362
(.leaf (.d 1 6 14))
(.leaf (.d 1 6 15)))))
(.branch 1366
(.branch 1364
(.leaf (.d 1 6 16))
(.branch 1365
(.leaf (.d 1 6 17))
(.leaf (.d 1 6 18))))
(.branch 1367
(.leaf (.d 1 6 19))
(.branch 1368
(.leaf (.d 1 6 20))
(.leaf (.d 1 6 21)))))))))))))
(.branch 2054
(.branch 1711
(.branch 1540
(.branch 1454
(.branch 1411
(.branch 1390
(.branch 1379
(.branch 1374
(.branch 1371
(.branch 1370
(.leaf (.d 2 6 7))
(.leaf (.d 2 6 8)))
(.branch 1372
(.leaf (.d 2 6 9))
(.branch 1373
(.leaf (.d 2 6 10))
(.leaf (.d 2 6 11)))))
(.branch 1376
(.branch 1375
(.leaf (.d 2 6 12))
(.leaf (.d 2 6 13)))
(.branch 1377
(.leaf (.d 2 6 14))
(.branch 1378
(.leaf (.d 2 6 15))
(.leaf (.d 2 6 16))))))
(.branch 1384
(.branch 1381
(.branch 1380
(.leaf (.d 2 6 17))
(.leaf (.d 2 6 18)))
(.branch 1382
(.leaf (.d 2 6 19))
(.branch 1383
(.leaf (.d 2 6 20))
(.leaf (.d 2 6 21)))))
(.branch 1387
(.branch 1385
(.leaf (.d 3 6 7))
(.branch 1386
(.leaf (.d 3 6 8))
(.leaf (.d 3 6 9))))
(.branch 1388
(.leaf (.d 3 6 10))
(.branch 1389
(.leaf (.d 3 6 11))
(.leaf (.d 3 6 12)))))))
(.branch 1400
(.branch 1395
(.branch 1392
(.branch 1391
(.leaf (.d 3 6 13))
(.leaf (.d 3 6 14)))
(.branch 1393
(.leaf (.d 3 6 15))
(.branch 1394
(.leaf (.d 3 6 16))
(.leaf (.d 3 6 17)))))
(.branch 1397
(.branch 1396
(.leaf (.d 3 6 18))
(.leaf (.d 3 6 19)))
(.branch 1398
(.leaf (.d 3 6 20))
(.branch 1399
(.leaf (.d 3 6 21))
(.leaf (.d 4 6 7))))))
(.branch 1405
(.branch 1402
(.branch 1401
(.leaf (.d 4 6 8))
(.leaf (.d 4 6 9)))
(.branch 1403
(.leaf (.d 4 6 10))
(.branch 1404
(.leaf (.d 4 6 11))
(.leaf (.d 4 6 12)))))
(.branch 1408
(.branch 1406
(.leaf (.d 4 6 13))
(.branch 1407
(.leaf (.d 4 6 14))
(.leaf (.d 4 6 15))))
(.branch 1409
(.leaf (.d 4 6 16))
(.branch 1410
(.leaf (.d 4 6 17))
(.leaf (.d 4 6 18))))))))
(.branch 1432
(.branch 1421
(.branch 1416
(.branch 1413
(.branch 1412
(.leaf (.d 4 6 19))
(.leaf (.d 4 6 20)))
(.branch 1414
(.leaf (.d 4 6 21))
(.branch 1415
(.leaf (.d 5 6 7))
(.leaf (.d 5 6 8)))))
(.branch 1418
(.branch 1417
(.leaf (.d 5 6 9))
(.leaf (.d 5 6 10)))
(.branch 1419
(.leaf (.d 5 6 11))
(.branch 1420
(.leaf (.d 5 6 12))
(.leaf (.d 5 6 13))))))
(.branch 1426
(.branch 1423
(.branch 1422
(.leaf (.d 5 6 14))
(.leaf (.d 5 6 15)))
(.branch 1424
(.leaf (.d 5 6 16))
(.branch 1425
(.leaf (.d 5 6 17))
(.leaf (.d 5 6 18)))))
(.branch 1429
(.branch 1427
(.leaf (.d 5 6 19))
(.branch 1428
(.leaf (.d 5 6 20))
(.leaf (.d 5 6 21))))
(.branch 1430
(.leaf (.d 6 6 7))
(.branch 1431
(.leaf (.d 6 6 8))
(.leaf (.d 6 6 9)))))))
(.branch 1443
(.branch 1437
(.branch 1434
(.branch 1433
(.leaf (.d 6 6 10))
(.leaf (.d 6 6 11)))
(.branch 1435
(.leaf (.d 6 6 12))
(.branch 1436
(.leaf (.d 6 6 13))
(.leaf (.d 6 6 14)))))
(.branch 1440
(.branch 1438
(.leaf (.d 6 6 15))
(.branch 1439
(.leaf (.d 6 6 16))
(.leaf (.d 6 6 17))))
(.branch 1441
(.leaf (.d 6 6 18))
(.branch 1442
(.leaf (.d 6 6 19))
(.leaf (.d 6 6 20))))))
(.branch 1448
(.branch 1445
(.branch 1444
(.leaf (.d 6 6 21))
(.leaf (.d 0 7 8)))
(.branch 1446
(.leaf (.d 0 7 9))
(.branch 1447
(.leaf (.d 0 7 10))
(.leaf (.d 0 7 11)))))
(.branch 1451
(.branch 1449
(.leaf (.d 0 7 12))
(.branch 1450
(.leaf (.d 0 7 13))
(.leaf (.d 0 7 14))))
(.branch 1452
(.leaf (.d 0 7 15))
(.branch 1453
(.leaf (.d 0 7 16))
(.leaf (.d 0 7 17)))))))))
(.branch 1497
(.branch 1475
(.branch 1464
(.branch 1459
(.branch 1456
(.branch 1455
(.leaf (.d 0 7 18))
(.leaf (.d 0 7 19)))
(.branch 1457
(.leaf (.d 0 7 20))
(.branch 1458
(.leaf (.d 0 7 21))
(.leaf (.d 1 7 8)))))
(.branch 1461
(.branch 1460
(.leaf (.d 1 7 9))
(.leaf (.d 1 7 10)))
(.branch 1462
(.leaf (.d 1 7 11))
(.branch 1463
(.leaf (.d 1 7 12))
(.leaf (.d 1 7 13))))))
(.branch 1469
(.branch 1466
(.branch 1465
(.leaf (.d 1 7 14))
(.leaf (.d 1 7 15)))
(.branch 1467
(.leaf (.d 1 7 16))
(.branch 1468
(.leaf (.d 1 7 17))
(.leaf (.d 1 7 18)))))
(.branch 1472
(.branch 1470
(.leaf (.d 1 7 19))
(.branch 1471
(.leaf (.d 1 7 20))
(.leaf (.d 1 7 21))))
(.branch 1473
(.leaf (.d 2 7 8))
(.branch 1474
(.leaf (.d 2 7 9))
(.leaf (.d 2 7 10)))))))
(.branch 1486
(.branch 1480
(.branch 1477
(.branch 1476
(.leaf (.d 2 7 11))
(.leaf (.d 2 7 12)))
(.branch 1478
(.leaf (.d 2 7 13))
(.branch 1479
(.leaf (.d 2 7 14))
(.leaf (.d 2 7 15)))))
(.branch 1483
(.branch 1481
(.leaf (.d 2 7 16))
(.branch 1482
(.leaf (.d 2 7 17))
(.leaf (.d 2 7 18))))
(.branch 1484
(.leaf (.d 2 7 19))
(.branch 1485
(.leaf (.d 2 7 20))
(.leaf (.d 2 7 21))))))
(.branch 1491
(.branch 1488
(.branch 1487
(.leaf (.d 3 7 8))
(.leaf (.d 3 7 9)))
(.branch 1489
(.leaf (.d 3 7 10))
(.branch 1490
(.leaf (.d 3 7 11))
(.leaf (.d 3 7 12)))))
(.branch 1494
(.branch 1492
(.leaf (.d 3 7 13))
(.branch 1493
(.leaf (.d 3 7 14))
(.leaf (.d 3 7 15))))
(.branch 1495
(.leaf (.d 3 7 16))
(.branch 1496
(.leaf (.d 3 7 17))
(.leaf (.d 3 7 18))))))))
(.branch 1518
(.branch 1507
(.branch 1502
(.branch 1499
(.branch 1498
(.leaf (.d 3 7 19))
(.leaf (.d 3 7 20)))
(.branch 1500
(.leaf (.d 3 7 21))
(.branch 1501
(.leaf (.d 4 7 8))
(.leaf (.d 4 7 9)))))
(.branch 1504
(.branch 1503
(.leaf (.d 4 7 10))
(.leaf (.d 4 7 11)))
(.branch 1505
(.leaf (.d 4 7 12))
(.branch 1506
(.leaf (.d 4 7 13))
(.leaf (.d 4 7 14))))))
(.branch 1512
(.branch 1509
(.branch 1508
(.leaf (.d 4 7 15))
(.leaf (.d 4 7 16)))
(.branch 1510
(.leaf (.d 4 7 17))
(.branch 1511
(.leaf (.d 4 7 18))
(.leaf (.d 4 7 19)))))
(.branch 1515
(.branch 1513
(.leaf (.d 4 7 20))
(.branch 1514
(.leaf (.d 4 7 21))
(.leaf (.d 5 7 8))))
(.branch 1516
(.leaf (.d 5 7 9))
(.branch 1517
(.leaf (.d 5 7 10))
(.leaf (.d 5 7 11)))))))
(.branch 1529
(.branch 1523
(.branch 1520
(.branch 1519
(.leaf (.d 5 7 12))
(.leaf (.d 5 7 13)))
(.branch 1521
(.leaf (.d 5 7 14))
(.branch 1522
(.leaf (.d 5 7 15))
(.leaf (.d 5 7 16)))))
(.branch 1526
(.branch 1524
(.leaf (.d 5 7 17))
(.branch 1525
(.leaf (.d 5 7 18))
(.leaf (.d 5 7 19))))
(.branch 1527
(.leaf (.d 5 7 20))
(.branch 1528
(.leaf (.d 5 7 21))
(.leaf (.d 6 7 8))))))
(.branch 1534
(.branch 1531
(.branch 1530
(.leaf (.d 6 7 9))
(.leaf (.d 6 7 10)))
(.branch 1532
(.leaf (.d 6 7 11))
(.branch 1533
(.leaf (.d 6 7 12))
(.leaf (.d 6 7 13)))))
(.branch 1537
(.branch 1535
(.leaf (.d 6 7 14))
(.branch 1536
(.leaf (.d 6 7 15))
(.leaf (.d 6 7 16))))
(.branch 1538
(.leaf (.d 6 7 17))
(.branch 1539
(.leaf (.d 6 7 18))
(.leaf (.d 6 7 19))))))))))
(.branch 1625
(.branch 1582
(.branch 1561
(.branch 1550
(.branch 1545
(.branch 1542
(.branch 1541
(.leaf (.d 6 7 20))
(.leaf (.d 6 7 21)))
(.branch 1543
(.leaf (.d 7 7 8))
(.branch 1544
(.leaf (.d 7 7 9))
(.leaf (.d 7 7 10)))))
(.branch 1547
(.branch 1546
(.leaf (.d 7 7 11))
(.leaf (.d 7 7 12)))
(.branch 1548
(.leaf (.d 7 7 13))
(.branch 1549
(.leaf (.d 7 7 14))
(.leaf (.d 7 7 15))))))
(.branch 1555
(.branch 1552
(.branch 1551
(.leaf (.d 7 7 16))
(.leaf (.d 7 7 17)))
(.branch 1553
(.leaf (.d 7 7 18))
(.branch 1554
(.leaf (.d 7 7 19))
(.leaf (.d 7 7 20)))))
(.branch 1558
(.branch 1556
(.leaf (.d 7 7 21))
(.branch 1557
(.leaf (.d 0 8 9))
(.leaf (.d 0 8 10))))
(.branch 1559
(.leaf (.d 0 8 11))
(.branch 1560
(.leaf (.d 0 8 12))
(.leaf (.d 0 8 13)))))))
(.branch 1571
(.branch 1566
(.branch 1563
(.branch 1562
(.leaf (.d 0 8 14))
(.leaf (.d 0 8 15)))
(.branch 1564
(.leaf (.d 0 8 16))
(.branch 1565
(.leaf (.d 0 8 17))
(.leaf (.d 0 8 18)))))
(.branch 1568
(.branch 1567
(.leaf (.d 0 8 19))
(.leaf (.d 0 8 20)))
(.branch 1569
(.leaf (.d 0 8 21))
(.branch 1570
(.leaf (.d 1 8 9))
(.leaf (.d 1 8 10))))))
(.branch 1576
(.branch 1573
(.branch 1572
(.leaf (.d 1 8 11))
(.leaf (.d 1 8 12)))
(.branch 1574
(.leaf (.d 1 8 13))
(.branch 1575
(.leaf (.d 1 8 14))
(.leaf (.d 1 8 15)))))
(.branch 1579
(.branch 1577
(.leaf (.d 1 8 16))
(.branch 1578
(.leaf (.d 1 8 17))
(.leaf (.d 1 8 18))))
(.branch 1580
(.leaf (.d 1 8 19))
(.branch 1581
(.leaf (.d 1 8 20))
(.leaf (.d 1 8 21))))))))
(.branch 1603
(.branch 1592
(.branch 1587
(.branch 1584
(.branch 1583
(.leaf (.d 2 8 9))
(.leaf (.d 2 8 10)))
(.branch 1585
(.leaf (.d 2 8 11))
(.branch 1586
(.leaf (.d 2 8 12))
(.leaf (.d 2 8 13)))))
(.branch 1589
(.branch 1588
(.leaf (.d 2 8 14))
(.leaf (.d 2 8 15)))
(.branch 1590
(.leaf (.d 2 8 16))
(.branch 1591
(.leaf (.d 2 8 17))
(.leaf (.d 2 8 18))))))
(.branch 1597
(.branch 1594
(.branch 1593
(.leaf (.d 2 8 19))
(.leaf (.d 2 8 20)))
(.branch 1595
(.leaf (.d 2 8 21))
(.branch 1596
(.leaf (.d 3 8 9))
(.leaf (.d 3 8 10)))))
(.branch 1600
(.branch 1598
(.leaf (.d 3 8 11))
(.branch 1599
(.leaf (.d 3 8 12))
(.leaf (.d 3 8 13))))
(.branch 1601
(.leaf (.d 3 8 14))
(.branch 1602
(.leaf (.d 3 8 15))
(.leaf (.d 3 8 16)))))))
(.branch 1614
(.branch 1608
(.branch 1605
(.branch 1604
(.leaf (.d 3 8 17))
(.leaf (.d 3 8 18)))
(.branch 1606
(.leaf (.d 3 8 19))
(.branch 1607
(.leaf (.d 3 8 20))
(.leaf (.d 3 8 21)))))
(.branch 1611
(.branch 1609
(.leaf (.d 4 8 9))
(.branch 1610
(.leaf (.d 4 8 10))
(.leaf (.d 4 8 11))))
(.branch 1612
(.leaf (.d 4 8 12))
(.branch 1613
(.leaf (.d 4 8 13))
(.leaf (.d 4 8 14))))))
(.branch 1619
(.branch 1616
(.branch 1615
(.leaf (.d 4 8 15))
(.leaf (.d 4 8 16)))
(.branch 1617
(.leaf (.d 4 8 17))
(.branch 1618
(.leaf (.d 4 8 18))
(.leaf (.d 4 8 19)))))
(.branch 1622
(.branch 1620
(.leaf (.d 4 8 20))
(.branch 1621
(.leaf (.d 4 8 21))
(.leaf (.d 5 8 9))))
(.branch 1623
(.leaf (.d 5 8 10))
(.branch 1624
(.leaf (.d 5 8 11))
(.leaf (.d 5 8 12)))))))))
(.branch 1668
(.branch 1646
(.branch 1635
(.branch 1630
(.branch 1627
(.branch 1626
(.leaf (.d 5 8 13))
(.leaf (.d 5 8 14)))
(.branch 1628
(.leaf (.d 5 8 15))
(.branch 1629
(.leaf (.d 5 8 16))
(.leaf (.d 5 8 17)))))
(.branch 1632
(.branch 1631
(.leaf (.d 5 8 18))
(.leaf (.d 5 8 19)))
(.branch 1633
(.leaf (.d 5 8 20))
(.branch 1634
(.leaf (.d 5 8 21))
(.leaf (.d 6 8 9))))))
(.branch 1640
(.branch 1637
(.branch 1636
(.leaf (.d 6 8 10))
(.leaf (.d 6 8 11)))
(.branch 1638
(.leaf (.d 6 8 12))
(.branch 1639
(.leaf (.d 6 8 13))
(.leaf (.d 6 8 14)))))
(.branch 1643
(.branch 1641
(.leaf (.d 6 8 15))
(.branch 1642
(.leaf (.d 6 8 16))
(.leaf (.d 6 8 17))))
(.branch 1644
(.leaf (.d 6 8 18))
(.branch 1645
(.leaf (.d 6 8 19))
(.leaf (.d 6 8 20)))))))
(.branch 1657
(.branch 1651
(.branch 1648
(.branch 1647
(.leaf (.d 6 8 21))
(.leaf (.d 7 8 9)))
(.branch 1649
(.leaf (.d 7 8 10))
(.branch 1650
(.leaf (.d 7 8 11))
(.leaf (.d 7 8 12)))))
(.branch 1654
(.branch 1652
(.leaf (.d 7 8 13))
(.branch 1653
(.leaf (.d 7 8 14))
(.leaf (.d 7 8 15))))
(.branch 1655
(.leaf (.d 7 8 16))
(.branch 1656
(.leaf (.d 7 8 17))
(.leaf (.d 7 8 18))))))
(.branch 1662
(.branch 1659
(.branch 1658
(.leaf (.d 7 8 19))
(.leaf (.d 7 8 20)))
(.branch 1660
(.leaf (.d 7 8 21))
(.branch 1661
(.leaf (.d 8 8 9))
(.leaf (.d 8 8 10)))))
(.branch 1665
(.branch 1663
(.leaf (.d 8 8 11))
(.branch 1664
(.leaf (.d 8 8 12))
(.leaf (.d 8 8 13))))
(.branch 1666
(.leaf (.d 8 8 14))
(.branch 1667
(.leaf (.d 8 8 15))
(.leaf (.d 8 8 16))))))))
(.branch 1689
(.branch 1678
(.branch 1673
(.branch 1670
(.branch 1669
(.leaf (.d 8 8 17))
(.leaf (.d 8 8 18)))
(.branch 1671
(.leaf (.d 8 8 19))
(.branch 1672
(.leaf (.d 8 8 20))
(.leaf (.d 8 8 21)))))
(.branch 1675
(.branch 1674
(.leaf (.d 0 9 10))
(.leaf (.d 0 9 11)))
(.branch 1676
(.leaf (.d 0 9 12))
(.branch 1677
(.leaf (.d 0 9 13))
(.leaf (.d 0 9 14))))))
(.branch 1683
(.branch 1680
(.branch 1679
(.leaf (.d 0 9 15))
(.leaf (.d 0 9 16)))
(.branch 1681
(.leaf (.d 0 9 17))
(.branch 1682
(.leaf (.d 0 9 18))
(.leaf (.d 0 9 19)))))
(.branch 1686
(.branch 1684
(.leaf (.d 0 9 20))
(.branch 1685
(.leaf (.d 0 9 21))
(.leaf (.d 1 9 10))))
(.branch 1687
(.leaf (.d 1 9 11))
(.branch 1688
(.leaf (.d 1 9 12))
(.leaf (.d 1 9 13)))))))
(.branch 1700
(.branch 1694
(.branch 1691
(.branch 1690
(.leaf (.d 1 9 14))
(.leaf (.d 1 9 15)))
(.branch 1692
(.leaf (.d 1 9 16))
(.branch 1693
(.leaf (.d 1 9 17))
(.leaf (.d 1 9 18)))))
(.branch 1697
(.branch 1695
(.leaf (.d 1 9 19))
(.branch 1696
(.leaf (.d 1 9 20))
(.leaf (.d 1 9 21))))
(.branch 1698
(.leaf (.d 2 9 10))
(.branch 1699
(.leaf (.d 2 9 11))
(.leaf (.d 2 9 12))))))
(.branch 1705
(.branch 1702
(.branch 1701
(.leaf (.d 2 9 13))
(.leaf (.d 2 9 14)))
(.branch 1703
(.leaf (.d 2 9 15))
(.branch 1704
(.leaf (.d 2 9 16))
(.leaf (.d 2 9 17)))))
(.branch 1708
(.branch 1706
(.leaf (.d 2 9 18))
(.branch 1707
(.leaf (.d 2 9 19))
(.leaf (.d 2 9 20))))
(.branch 1709
(.leaf (.d 2 9 21))
(.branch 1710
(.leaf (.d 3 9 10))
(.leaf (.d 3 9 11)))))))))))
(.branch 1882
(.branch 1796
(.branch 1753
(.branch 1732
(.branch 1721
(.branch 1716
(.branch 1713
(.branch 1712
(.leaf (.d 3 9 12))
(.leaf (.d 3 9 13)))
(.branch 1714
(.leaf (.d 3 9 14))
(.branch 1715
(.leaf (.d 3 9 15))
(.leaf (.d 3 9 16)))))
(.branch 1718
(.branch 1717
(.leaf (.d 3 9 17))
(.leaf (.d 3 9 18)))
(.branch 1719
(.leaf (.d 3 9 19))
(.branch 1720
(.leaf (.d 3 9 20))
(.leaf (.d 3 9 21))))))
(.branch 1726
(.branch 1723
(.branch 1722
(.leaf (.d 4 9 10))
(.leaf (.d 4 9 11)))
(.branch 1724
(.leaf (.d 4 9 12))
(.branch 1725
(.leaf (.d 4 9 13))
(.leaf (.d 4 9 14)))))
(.branch 1729
(.branch 1727
(.leaf (.d 4 9 15))
(.branch 1728
(.leaf (.d 4 9 16))
(.leaf (.d 4 9 17))))
(.branch 1730
(.leaf (.d 4 9 18))
(.branch 1731
(.leaf (.d 4 9 19))
(.leaf (.d 4 9 20)))))))
(.branch 1742
(.branch 1737
(.branch 1734
(.branch 1733
(.leaf (.d 4 9 21))
(.leaf (.d 5 9 10)))
(.branch 1735
(.leaf (.d 5 9 11))
(.branch 1736
(.leaf (.d 5 9 12))
(.leaf (.d 5 9 13)))))
(.branch 1739
(.branch 1738
(.leaf (.d 5 9 14))
(.leaf (.d 5 9 15)))
(.branch 1740
(.leaf (.d 5 9 16))
(.branch 1741
(.leaf (.d 5 9 17))
(.leaf (.d 5 9 18))))))
(.branch 1747
(.branch 1744
(.branch 1743
(.leaf (.d 5 9 19))
(.leaf (.d 5 9 20)))
(.branch 1745
(.leaf (.d 5 9 21))
(.branch 1746
(.leaf (.d 6 9 10))
(.leaf (.d 6 9 11)))))
(.branch 1750
(.branch 1748
(.leaf (.d 6 9 12))
(.branch 1749
(.leaf (.d 6 9 13))
(.leaf (.d 6 9 14))))
(.branch 1751
(.leaf (.d 6 9 15))
(.branch 1752
(.leaf (.d 6 9 16))
(.leaf (.d 6 9 17))))))))
(.branch 1774
(.branch 1763
(.branch 1758
(.branch 1755
(.branch 1754
(.leaf (.d 6 9 18))
(.leaf (.d 6 9 19)))
(.branch 1756
(.leaf (.d 6 9 20))
(.branch 1757
(.leaf (.d 6 9 21))
(.leaf (.d 7 9 10)))))
(.branch 1760
(.branch 1759
(.leaf (.d 7 9 11))
(.leaf (.d 7 9 12)))
(.branch 1761
(.leaf (.d 7 9 13))
(.branch 1762
(.leaf (.d 7 9 14))
(.leaf (.d 7 9 15))))))
(.branch 1768
(.branch 1765
(.branch 1764
(.leaf (.d 7 9 16))
(.leaf (.d 7 9 17)))
(.branch 1766
(.leaf (.d 7 9 18))
(.branch 1767
(.leaf (.d 7 9 19))
(.leaf (.d 7 9 20)))))
(.branch 1771
(.branch 1769
(.leaf (.d 7 9 21))
(.branch 1770
(.leaf (.d 8 9 10))
(.leaf (.d 8 9 11))))
(.branch 1772
(.leaf (.d 8 9 12))
(.branch 1773
(.leaf (.d 8 9 13))
(.leaf (.d 8 9 14)))))))
(.branch 1785
(.branch 1779
(.branch 1776
(.branch 1775
(.leaf (.d 8 9 15))
(.leaf (.d 8 9 16)))
(.branch 1777
(.leaf (.d 8 9 17))
(.branch 1778
(.leaf (.d 8 9 18))
(.leaf (.d 8 9 19)))))
(.branch 1782
(.branch 1780
(.leaf (.d 8 9 20))
(.branch 1781
(.leaf (.d 8 9 21))
(.leaf (.d 9 9 10))))
(.branch 1783
(.leaf (.d 9 9 11))
(.branch 1784
(.leaf (.d 9 9 12))
(.leaf (.d 9 9 13))))))
(.branch 1790
(.branch 1787
(.branch 1786
(.leaf (.d 9 9 14))
(.leaf (.d 9 9 15)))
(.branch 1788
(.leaf (.d 9 9 16))
(.branch 1789
(.leaf (.d 9 9 17))
(.leaf (.d 9 9 18)))))
(.branch 1793
(.branch 1791
(.leaf (.d 9 9 19))
(.branch 1792
(.leaf (.d 9 9 20))
(.leaf (.d 9 9 21))))
(.branch 1794
(.leaf (.d 0 10 11))
(.branch 1795
(.leaf (.d 0 10 12))
(.leaf (.d 0 10 13)))))))))
(.branch 1839
(.branch 1817
(.branch 1806
(.branch 1801
(.branch 1798
(.branch 1797
(.leaf (.d 0 10 14))
(.leaf (.d 0 10 15)))
(.branch 1799
(.leaf (.d 0 10 16))
(.branch 1800
(.leaf (.d 0 10 17))
(.leaf (.d 0 10 18)))))
(.branch 1803
(.branch 1802
(.leaf (.d 0 10 19))
(.leaf (.d 0 10 20)))
(.branch 1804
(.leaf (.d 0 10 21))
(.branch 1805
(.leaf (.d 1 10 11))
(.leaf (.d 1 10 12))))))
(.branch 1811
(.branch 1808
(.branch 1807
(.leaf (.d 1 10 13))
(.leaf (.d 1 10 14)))
(.branch 1809
(.leaf (.d 1 10 15))
(.branch 1810
(.leaf (.d 1 10 16))
(.leaf (.d 1 10 17)))))
(.branch 1814
(.branch 1812
(.leaf (.d 1 10 18))
(.branch 1813
(.leaf (.d 1 10 19))
(.leaf (.d 1 10 20))))
(.branch 1815
(.leaf (.d 1 10 21))
(.branch 1816
(.leaf (.d 2 10 11))
(.leaf (.d 2 10 12)))))))
(.branch 1828
(.branch 1822
(.branch 1819
(.branch 1818
(.leaf (.d 2 10 13))
(.leaf (.d 2 10 14)))
(.branch 1820
(.leaf (.d 2 10 15))
(.branch 1821
(.leaf (.d 2 10 16))
(.leaf (.d 2 10 17)))))
(.branch 1825
(.branch 1823
(.leaf (.d 2 10 18))
(.branch 1824
(.leaf (.d 2 10 19))
(.leaf (.d 2 10 20))))
(.branch 1826
(.leaf (.d 2 10 21))
(.branch 1827
(.leaf (.d 3 10 11))
(.leaf (.d 3 10 12))))))
(.branch 1833
(.branch 1830
(.branch 1829
(.leaf (.d 3 10 13))
(.leaf (.d 3 10 14)))
(.branch 1831
(.leaf (.d 3 10 15))
(.branch 1832
(.leaf (.d 3 10 16))
(.leaf (.d 3 10 17)))))
(.branch 1836
(.branch 1834
(.leaf (.d 3 10 18))
(.branch 1835
(.leaf (.d 3 10 19))
(.leaf (.d 3 10 20))))
(.branch 1837
(.leaf (.d 3 10 21))
(.branch 1838
(.leaf (.d 4 10 11))
(.leaf (.d 4 10 12))))))))
(.branch 1860
(.branch 1849
(.branch 1844
(.branch 1841
(.branch 1840
(.leaf (.d 4 10 13))
(.leaf (.d 4 10 14)))
(.branch 1842
(.leaf (.d 4 10 15))
(.branch 1843
(.leaf (.d 4 10 16))
(.leaf (.d 4 10 17)))))
(.branch 1846
(.branch 1845
(.leaf (.d 4 10 18))
(.leaf (.d 4 10 19)))
(.branch 1847
(.leaf (.d 4 10 20))
(.branch 1848
(.leaf (.d 4 10 21))
(.leaf (.d 5 10 11))))))
(.branch 1854
(.branch 1851
(.branch 1850
(.leaf (.d 5 10 12))
(.leaf (.d 5 10 13)))
(.branch 1852
(.leaf (.d 5 10 14))
(.branch 1853
(.leaf (.d 5 10 15))
(.leaf (.d 5 10 16)))))
(.branch 1857
(.branch 1855
(.leaf (.d 5 10 17))
(.branch 1856
(.leaf (.d 5 10 18))
(.leaf (.d 5 10 19))))
(.branch 1858
(.leaf (.d 5 10 20))
(.branch 1859
(.leaf (.d 5 10 21))
(.leaf (.d 6 10 11)))))))
(.branch 1871
(.branch 1865
(.branch 1862
(.branch 1861
(.leaf (.d 6 10 12))
(.leaf (.d 6 10 13)))
(.branch 1863
(.leaf (.d 6 10 14))
(.branch 1864
(.leaf (.d 6 10 15))
(.leaf (.d 6 10 16)))))
(.branch 1868
(.branch 1866
(.leaf (.d 6 10 17))
(.branch 1867
(.leaf (.d 6 10 18))
(.leaf (.d 6 10 19))))
(.branch 1869
(.leaf (.d 6 10 20))
(.branch 1870
(.leaf (.d 6 10 21))
(.leaf (.d 7 10 11))))))
(.branch 1876
(.branch 1873
(.branch 1872
(.leaf (.d 7 10 12))
(.leaf (.d 7 10 13)))
(.branch 1874
(.leaf (.d 7 10 14))
(.branch 1875
(.leaf (.d 7 10 15))
(.leaf (.d 7 10 16)))))
(.branch 1879
(.branch 1877
(.leaf (.d 7 10 17))
(.branch 1878
(.leaf (.d 7 10 18))
(.leaf (.d 7 10 19))))
(.branch 1880
(.leaf (.d 7 10 20))
(.branch 1881
(.leaf (.d 7 10 21))
(.leaf (.d 8 10 11))))))))))
(.branch 1968
(.branch 1925
(.branch 1903
(.branch 1892
(.branch 1887
(.branch 1884
(.branch 1883
(.leaf (.d 8 10 12))
(.leaf (.d 8 10 13)))
(.branch 1885
(.leaf (.d 8 10 14))
(.branch 1886
(.leaf (.d 8 10 15))
(.leaf (.d 8 10 16)))))
(.branch 1889
(.branch 1888
(.leaf (.d 8 10 17))
(.leaf (.d 8 10 18)))
(.branch 1890
(.leaf (.d 8 10 19))
(.branch 1891
(.leaf (.d 8 10 20))
(.leaf (.d 8 10 21))))))
(.branch 1897
(.branch 1894
(.branch 1893
(.leaf (.d 9 10 11))
(.leaf (.d 9 10 12)))
(.branch 1895
(.leaf (.d 9 10 13))
(.branch 1896
(.leaf (.d 9 10 14))
(.leaf (.d 9 10 15)))))
(.branch 1900
(.branch 1898
(.leaf (.d 9 10 16))
(.branch 1899
(.leaf (.d 9 10 17))
(.leaf (.d 9 10 18))))
(.branch 1901
(.leaf (.d 9 10 19))
(.branch 1902
(.leaf (.d 9 10 20))
(.leaf (.d 9 10 21)))))))
(.branch 1914
(.branch 1908
(.branch 1905
(.branch 1904
(.leaf (.d 10 10 11))
(.leaf (.d 10 10 12)))
(.branch 1906
(.leaf (.d 10 10 13))
(.branch 1907
(.leaf (.d 10 10 14))
(.leaf (.d 10 10 15)))))
(.branch 1911
(.branch 1909
(.leaf (.d 10 10 16))
(.branch 1910
(.leaf (.d 10 10 17))
(.leaf (.d 10 10 18))))
(.branch 1912
(.leaf (.d 10 10 19))
(.branch 1913
(.leaf (.d 10 10 20))
(.leaf (.d 10 10 21))))))
(.branch 1919
(.branch 1916
(.branch 1915
(.leaf (.d 0 11 12))
(.leaf (.d 0 11 13)))
(.branch 1917
(.leaf (.d 0 11 14))
(.branch 1918
(.leaf (.d 0 11 15))
(.leaf (.d 0 11 16)))))
(.branch 1922
(.branch 1920
(.leaf (.d 0 11 17))
(.branch 1921
(.leaf (.d 0 11 18))
(.leaf (.d 0 11 19))))
(.branch 1923
(.leaf (.d 0 11 20))
(.branch 1924
(.leaf (.d 0 11 21))
(.leaf (.d 1 11 12))))))))
(.branch 1946
(.branch 1935
(.branch 1930
(.branch 1927
(.branch 1926
(.leaf (.d 1 11 13))
(.leaf (.d 1 11 14)))
(.branch 1928
(.leaf (.d 1 11 15))
(.branch 1929
(.leaf (.d 1 11 16))
(.leaf (.d 1 11 17)))))
(.branch 1932
(.branch 1931
(.leaf (.d 1 11 18))
(.leaf (.d 1 11 19)))
(.branch 1933
(.leaf (.d 1 11 20))
(.branch 1934
(.leaf (.d 1 11 21))
(.leaf (.d 2 11 12))))))
(.branch 1940
(.branch 1937
(.branch 1936
(.leaf (.d 2 11 13))
(.leaf (.d 2 11 14)))
(.branch 1938
(.leaf (.d 2 11 15))
(.branch 1939
(.leaf (.d 2 11 16))
(.leaf (.d 2 11 17)))))
(.branch 1943
(.branch 1941
(.leaf (.d 2 11 18))
(.branch 1942
(.leaf (.d 2 11 19))
(.leaf (.d 2 11 20))))
(.branch 1944
(.leaf (.d 2 11 21))
(.branch 1945
(.leaf (.d 3 11 12))
(.leaf (.d 3 11 13)))))))
(.branch 1957
(.branch 1951
(.branch 1948
(.branch 1947
(.leaf (.d 3 11 14))
(.leaf (.d 3 11 15)))
(.branch 1949
(.leaf (.d 3 11 16))
(.branch 1950
(.leaf (.d 3 11 17))
(.leaf (.d 3 11 18)))))
(.branch 1954
(.branch 1952
(.leaf (.d 3 11 19))
(.branch 1953
(.leaf (.d 3 11 20))
(.leaf (.d 3 11 21))))
(.branch 1955
(.leaf (.d 4 11 12))
(.branch 1956
(.leaf (.d 4 11 13))
(.leaf (.d 4 11 14))))))
(.branch 1962
(.branch 1959
(.branch 1958
(.leaf (.d 4 11 15))
(.leaf (.d 4 11 16)))
(.branch 1960
(.leaf (.d 4 11 17))
(.branch 1961
(.leaf (.d 4 11 18))
(.leaf (.d 4 11 19)))))
(.branch 1965
(.branch 1963
(.leaf (.d 4 11 20))
(.branch 1964
(.leaf (.d 4 11 21))
(.leaf (.d 5 11 12))))
(.branch 1966
(.leaf (.d 5 11 13))
(.branch 1967
(.leaf (.d 5 11 14))
(.leaf (.d 5 11 15)))))))))
(.branch 2011
(.branch 1989
(.branch 1978
(.branch 1973
(.branch 1970
(.branch 1969
(.leaf (.d 5 11 16))
(.leaf (.d 5 11 17)))
(.branch 1971
(.leaf (.d 5 11 18))
(.branch 1972
(.leaf (.d 5 11 19))
(.leaf (.d 5 11 20)))))
(.branch 1975
(.branch 1974
(.leaf (.d 5 11 21))
(.leaf (.d 6 11 12)))
(.branch 1976
(.leaf (.d 6 11 13))
(.branch 1977
(.leaf (.d 6 11 14))
(.leaf (.d 6 11 15))))))
(.branch 1983
(.branch 1980
(.branch 1979
(.leaf (.d 6 11 16))
(.leaf (.d 6 11 17)))
(.branch 1981
(.leaf (.d 6 11 18))
(.branch 1982
(.leaf (.d 6 11 19))
(.leaf (.d 6 11 20)))))
(.branch 1986
(.branch 1984
(.leaf (.d 6 11 21))
(.branch 1985
(.leaf (.d 7 11 12))
(.leaf (.d 7 11 13))))
(.branch 1987
(.leaf (.d 7 11 14))
(.branch 1988
(.leaf (.d 7 11 15))
(.leaf (.d 7 11 16)))))))
(.branch 2000
(.branch 1994
(.branch 1991
(.branch 1990
(.leaf (.d 7 11 17))
(.leaf (.d 7 11 18)))
(.branch 1992
(.leaf (.d 7 11 19))
(.branch 1993
(.leaf (.d 7 11 20))
(.leaf (.d 7 11 21)))))
(.branch 1997
(.branch 1995
(.leaf (.d 8 11 12))
(.branch 1996
(.leaf (.d 8 11 13))
(.leaf (.d 8 11 14))))
(.branch 1998
(.leaf (.d 8 11 15))
(.branch 1999
(.leaf (.d 8 11 16))
(.leaf (.d 8 11 17))))))
(.branch 2005
(.branch 2002
(.branch 2001
(.leaf (.d 8 11 18))
(.leaf (.d 8 11 19)))
(.branch 2003
(.leaf (.d 8 11 20))
(.branch 2004
(.leaf (.d 8 11 21))
(.leaf (.d 9 11 12)))))
(.branch 2008
(.branch 2006
(.leaf (.d 9 11 13))
(.branch 2007
(.leaf (.d 9 11 14))
(.leaf (.d 9 11 15))))
(.branch 2009
(.leaf (.d 9 11 16))
(.branch 2010
(.leaf (.d 9 11 17))
(.leaf (.d 9 11 18))))))))
(.branch 2032
(.branch 2021
(.branch 2016
(.branch 2013
(.branch 2012
(.leaf (.d 9 11 19))
(.leaf (.d 9 11 20)))
(.branch 2014
(.leaf (.d 9 11 21))
(.branch 2015
(.leaf (.d 10 11 12))
(.leaf (.d 10 11 13)))))
(.branch 2018
(.branch 2017
(.leaf (.d 10 11 14))
(.leaf (.d 10 11 15)))
(.branch 2019
(.leaf (.d 10 11 16))
(.branch 2020
(.leaf (.d 10 11 17))
(.leaf (.d 10 11 18))))))
(.branch 2026
(.branch 2023
(.branch 2022
(.leaf (.d 10 11 19))
(.leaf (.d 10 11 20)))
(.branch 2024
(.leaf (.d 10 11 21))
(.branch 2025
(.leaf (.d 11 11 12))
(.leaf (.d 11 11 13)))))
(.branch 2029
(.branch 2027
(.leaf (.d 11 11 14))
(.branch 2028
(.leaf (.d 11 11 15))
(.leaf (.d 11 11 16))))
(.branch 2030
(.leaf (.d 11 11 17))
(.branch 2031
(.leaf (.d 11 11 18))
(.leaf (.d 11 11 19)))))))
(.branch 2043
(.branch 2037
(.branch 2034
(.branch 2033
(.leaf (.d 11 11 20))
(.leaf (.d 11 11 21)))
(.branch 2035
(.leaf (.d 0 12 13))
(.branch 2036
(.leaf (.d 0 12 14))
(.leaf (.d 0 12 15)))))
(.branch 2040
(.branch 2038
(.leaf (.d 0 12 16))
(.branch 2039
(.leaf (.d 0 12 17))
(.leaf (.d 0 12 18))))
(.branch 2041
(.leaf (.d 0 12 19))
(.branch 2042
(.leaf (.d 0 12 20))
(.leaf (.d 0 12 21))))))
(.branch 2048
(.branch 2045
(.branch 2044
(.leaf (.d 1 12 13))
(.leaf (.d 1 12 14)))
(.branch 2046
(.leaf (.d 1 12 15))
(.branch 2047
(.leaf (.d 1 12 16))
(.leaf (.d 1 12 17)))))
(.branch 2051
(.branch 2049
(.leaf (.d 1 12 18))
(.branch 2050
(.leaf (.d 1 12 19))
(.leaf (.d 1 12 20))))
(.branch 2052
(.leaf (.d 1 12 21))
(.branch 2053
(.leaf (.d 2 12 13))
(.leaf (.d 2 12 14))))))))))))
(.branch 2396
(.branch 2225
(.branch 2139
(.branch 2096
(.branch 2075
(.branch 2064
(.branch 2059
(.branch 2056
(.branch 2055
(.leaf (.d 2 12 15))
(.leaf (.d 2 12 16)))
(.branch 2057
(.leaf (.d 2 12 17))
(.branch 2058
(.leaf (.d 2 12 18))
(.leaf (.d 2 12 19)))))
(.branch 2061
(.branch 2060
(.leaf (.d 2 12 20))
(.leaf (.d 2 12 21)))
(.branch 2062
(.leaf (.d 3 12 13))
(.branch 2063
(.leaf (.d 3 12 14))
(.leaf (.d 3 12 15))))))
(.branch 2069
(.branch 2066
(.branch 2065
(.leaf (.d 3 12 16))
(.leaf (.d 3 12 17)))
(.branch 2067
(.leaf (.d 3 12 18))
(.branch 2068
(.leaf (.d 3 12 19))
(.leaf (.d 3 12 20)))))
(.branch 2072
(.branch 2070
(.leaf (.d 3 12 21))
(.branch 2071
(.leaf (.d 4 12 13))
(.leaf (.d 4 12 14))))
(.branch 2073
(.leaf (.d 4 12 15))
(.branch 2074
(.leaf (.d 4 12 16))
(.leaf (.d 4 12 17)))))))
(.branch 2085
(.branch 2080
(.branch 2077
(.branch 2076
(.leaf (.d 4 12 18))
(.leaf (.d 4 12 19)))
(.branch 2078
(.leaf (.d 4 12 20))
(.branch 2079
(.leaf (.d 4 12 21))
(.leaf (.d 5 12 13)))))
(.branch 2082
(.branch 2081
(.leaf (.d 5 12 14))
(.leaf (.d 5 12 15)))
(.branch 2083
(.leaf (.d 5 12 16))
(.branch 2084
(.leaf (.d 5 12 17))
(.leaf (.d 5 12 18))))))
(.branch 2090
(.branch 2087
(.branch 2086
(.leaf (.d 5 12 19))
(.leaf (.d 5 12 20)))
(.branch 2088
(.leaf (.d 5 12 21))
(.branch 2089
(.leaf (.d 6 12 13))
(.leaf (.d 6 12 14)))))
(.branch 2093
(.branch 2091
(.leaf (.d 6 12 15))
(.branch 2092
(.leaf (.d 6 12 16))
(.leaf (.d 6 12 17))))
(.branch 2094
(.leaf (.d 6 12 18))
(.branch 2095
(.leaf (.d 6 12 19))
(.leaf (.d 6 12 20))))))))
(.branch 2117
(.branch 2106
(.branch 2101
(.branch 2098
(.branch 2097
(.leaf (.d 6 12 21))
(.leaf (.d 7 12 13)))
(.branch 2099
(.leaf (.d 7 12 14))
(.branch 2100
(.leaf (.d 7 12 15))
(.leaf (.d 7 12 16)))))
(.branch 2103
(.branch 2102
(.leaf (.d 7 12 17))
(.leaf (.d 7 12 18)))
(.branch 2104
(.leaf (.d 7 12 19))
(.branch 2105
(.leaf (.d 7 12 20))
(.leaf (.d 7 12 21))))))
(.branch 2111
(.branch 2108
(.branch 2107
(.leaf (.d 8 12 13))
(.leaf (.d 8 12 14)))
(.branch 2109
(.leaf (.d 8 12 15))
(.branch 2110
(.leaf (.d 8 12 16))
(.leaf (.d 8 12 17)))))
(.branch 2114
(.branch 2112
(.leaf (.d 8 12 18))
(.branch 2113
(.leaf (.d 8 12 19))
(.leaf (.d 8 12 20))))
(.branch 2115
(.leaf (.d 8 12 21))
(.branch 2116
(.leaf (.d 9 12 13))
(.leaf (.d 9 12 14)))))))
(.branch 2128
(.branch 2122
(.branch 2119
(.branch 2118
(.leaf (.d 9 12 15))
(.leaf (.d 9 12 16)))
(.branch 2120
(.leaf (.d 9 12 17))
(.branch 2121
(.leaf (.d 9 12 18))
(.leaf (.d 9 12 19)))))
(.branch 2125
(.branch 2123
(.leaf (.d 9 12 20))
(.branch 2124
(.leaf (.d 9 12 21))
(.leaf (.d 10 12 13))))
(.branch 2126
(.leaf (.d 10 12 14))
(.branch 2127
(.leaf (.d 10 12 15))
(.leaf (.d 10 12 16))))))
(.branch 2133
(.branch 2130
(.branch 2129
(.leaf (.d 10 12 17))
(.leaf (.d 10 12 18)))
(.branch 2131
(.leaf (.d 10 12 19))
(.branch 2132
(.leaf (.d 10 12 20))
(.leaf (.d 10 12 21)))))
(.branch 2136
(.branch 2134
(.leaf (.d 11 12 13))
(.branch 2135
(.leaf (.d 11 12 14))
(.leaf (.d 11 12 15))))
(.branch 2137
(.leaf (.d 11 12 16))
(.branch 2138
(.leaf (.d 11 12 17))
(.leaf (.d 11 12 18)))))))))
(.branch 2182
(.branch 2160
(.branch 2149
(.branch 2144
(.branch 2141
(.branch 2140
(.leaf (.d 11 12 19))
(.leaf (.d 11 12 20)))
(.branch 2142
(.leaf (.d 11 12 21))
(.branch 2143
(.leaf (.d 12 12 13))
(.leaf (.d 12 12 14)))))
(.branch 2146
(.branch 2145
(.leaf (.d 12 12 15))
(.leaf (.d 12 12 16)))
(.branch 2147
(.leaf (.d 12 12 17))
(.branch 2148
(.leaf (.d 12 12 18))
(.leaf (.d 12 12 19))))))
(.branch 2154
(.branch 2151
(.branch 2150
(.leaf (.d 12 12 20))
(.leaf (.d 12 12 21)))
(.branch 2152
(.leaf (.d 0 13 14))
(.branch 2153
(.leaf (.d 0 13 15))
(.leaf (.d 0 13 16)))))
(.branch 2157
(.branch 2155
(.leaf (.d 0 13 17))
(.branch 2156
(.leaf (.d 0 13 18))
(.leaf (.d 0 13 19))))
(.branch 2158
(.leaf (.d 0 13 20))
(.branch 2159
(.leaf (.d 0 13 21))
(.leaf (.d 1 13 14)))))))
(.branch 2171
(.branch 2165
(.branch 2162
(.branch 2161
(.leaf (.d 1 13 15))
(.leaf (.d 1 13 16)))
(.branch 2163
(.leaf (.d 1 13 17))
(.branch 2164
(.leaf (.d 1 13 18))
(.leaf (.d 1 13 19)))))
(.branch 2168
(.branch 2166
(.leaf (.d 1 13 20))
(.branch 2167
(.leaf (.d 1 13 21))
(.leaf (.d 2 13 14))))
(.branch 2169
(.leaf (.d 2 13 15))
(.branch 2170
(.leaf (.d 2 13 16))
(.leaf (.d 2 13 17))))))
(.branch 2176
(.branch 2173
(.branch 2172
(.leaf (.d 2 13 18))
(.leaf (.d 2 13 19)))
(.branch 2174
(.leaf (.d 2 13 20))
(.branch 2175
(.leaf (.d 2 13 21))
(.leaf (.d 3 13 14)))))
(.branch 2179
(.branch 2177
(.leaf (.d 3 13 15))
(.branch 2178
(.leaf (.d 3 13 16))
(.leaf (.d 3 13 17))))
(.branch 2180
(.leaf (.d 3 13 18))
(.branch 2181
(.leaf (.d 3 13 19))
(.leaf (.d 3 13 20))))))))
(.branch 2203
(.branch 2192
(.branch 2187
(.branch 2184
(.branch 2183
(.leaf (.d 3 13 21))
(.leaf (.d 4 13 14)))
(.branch 2185
(.leaf (.d 4 13 15))
(.branch 2186
(.leaf (.d 4 13 16))
(.leaf (.d 4 13 17)))))
(.branch 2189
(.branch 2188
(.leaf (.d 4 13 18))
(.leaf (.d 4 13 19)))
(.branch 2190
(.leaf (.d 4 13 20))
(.branch 2191
(.leaf (.d 4 13 21))
(.leaf (.d 5 13 14))))))
(.branch 2197
(.branch 2194
(.branch 2193
(.leaf (.d 5 13 15))
(.leaf (.d 5 13 16)))
(.branch 2195
(.leaf (.d 5 13 17))
(.branch 2196
(.leaf (.d 5 13 18))
(.leaf (.d 5 13 19)))))
(.branch 2200
(.branch 2198
(.leaf (.d 5 13 20))
(.branch 2199
(.leaf (.d 5 13 21))
(.leaf (.d 6 13 14))))
(.branch 2201
(.leaf (.d 6 13 15))
(.branch 2202
(.leaf (.d 6 13 16))
(.leaf (.d 6 13 17)))))))
(.branch 2214
(.branch 2208
(.branch 2205
(.branch 2204
(.leaf (.d 6 13 18))
(.leaf (.d 6 13 19)))
(.branch 2206
(.leaf (.d 6 13 20))
(.branch 2207
(.leaf (.d 6 13 21))
(.leaf (.d 7 13 14)))))
(.branch 2211
(.branch 2209
(.leaf (.d 7 13 15))
(.branch 2210
(.leaf (.d 7 13 16))
(.leaf (.d 7 13 17))))
(.branch 2212
(.leaf (.d 7 13 18))
(.branch 2213
(.leaf (.d 7 13 19))
(.leaf (.d 7 13 20))))))
(.branch 2219
(.branch 2216
(.branch 2215
(.leaf (.d 7 13 21))
(.leaf (.d 8 13 14)))
(.branch 2217
(.leaf (.d 8 13 15))
(.branch 2218
(.leaf (.d 8 13 16))
(.leaf (.d 8 13 17)))))
(.branch 2222
(.branch 2220
(.leaf (.d 8 13 18))
(.branch 2221
(.leaf (.d 8 13 19))
(.leaf (.d 8 13 20))))
(.branch 2223
(.leaf (.d 8 13 21))
(.branch 2224
(.leaf (.d 9 13 14))
(.leaf (.d 9 13 15))))))))))
(.branch 2310
(.branch 2267
(.branch 2246
(.branch 2235
(.branch 2230
(.branch 2227
(.branch 2226
(.leaf (.d 9 13 16))
(.leaf (.d 9 13 17)))
(.branch 2228
(.leaf (.d 9 13 18))
(.branch 2229
(.leaf (.d 9 13 19))
(.leaf (.d 9 13 20)))))
(.branch 2232
(.branch 2231
(.leaf (.d 9 13 21))
(.leaf (.d 10 13 14)))
(.branch 2233
(.leaf (.d 10 13 15))
(.branch 2234
(.leaf (.d 10 13 16))
(.leaf (.d 10 13 17))))))
(.branch 2240
(.branch 2237
(.branch 2236
(.leaf (.d 10 13 18))
(.leaf (.d 10 13 19)))
(.branch 2238
(.leaf (.d 10 13 20))
(.branch 2239
(.leaf (.d 10 13 21))
(.leaf (.d 11 13 14)))))
(.branch 2243
(.branch 2241
(.leaf (.d 11 13 15))
(.branch 2242
(.leaf (.d 11 13 16))
(.leaf (.d 11 13 17))))
(.branch 2244
(.leaf (.d 11 13 18))
(.branch 2245
(.leaf (.d 11 13 19))
(.leaf (.d 11 13 20)))))))
(.branch 2256
(.branch 2251
(.branch 2248
(.branch 2247
(.leaf (.d 11 13 21))
(.leaf (.d 12 13 14)))
(.branch 2249
(.leaf (.d 12 13 15))
(.branch 2250
(.leaf (.d 12 13 16))
(.leaf (.d 12 13 17)))))
(.branch 2253
(.branch 2252
(.leaf (.d 12 13 18))
(.leaf (.d 12 13 19)))
(.branch 2254
(.leaf (.d 12 13 20))
(.branch 2255
(.leaf (.d 12 13 21))
(.leaf (.d 13 13 14))))))
(.branch 2261
(.branch 2258
(.branch 2257
(.leaf (.d 13 13 15))
(.leaf (.d 13 13 16)))
(.branch 2259
(.leaf (.d 13 13 17))
(.branch 2260
(.leaf (.d 13 13 18))
(.leaf (.d 13 13 19)))))
(.branch 2264
(.branch 2262
(.leaf (.d 13 13 20))
(.branch 2263
(.leaf (.d 13 13 21))
(.leaf (.d 0 14 15))))
(.branch 2265
(.leaf (.d 0 14 16))
(.branch 2266
(.leaf (.d 0 14 17))
(.leaf (.d 0 14 18))))))))
(.branch 2288
(.branch 2277
(.branch 2272
(.branch 2269
(.branch 2268
(.leaf (.d 0 14 19))
(.leaf (.d 0 14 20)))
(.branch 2270
(.leaf (.d 0 14 21))
(.branch 2271
(.leaf (.d 1 14 15))
(.leaf (.d 1 14 16)))))
(.branch 2274
(.branch 2273
(.leaf (.d 1 14 17))
(.leaf (.d 1 14 18)))
(.branch 2275
(.leaf (.d 1 14 19))
(.branch 2276
(.leaf (.d 1 14 20))
(.leaf (.d 1 14 21))))))
(.branch 2282
(.branch 2279
(.branch 2278
(.leaf (.d 2 14 15))
(.leaf (.d 2 14 16)))
(.branch 2280
(.leaf (.d 2 14 17))
(.branch 2281
(.leaf (.d 2 14 18))
(.leaf (.d 2 14 19)))))
(.branch 2285
(.branch 2283
(.leaf (.d 2 14 20))
(.branch 2284
(.leaf (.d 2 14 21))
(.leaf (.d 3 14 15))))
(.branch 2286
(.leaf (.d 3 14 16))
(.branch 2287
(.leaf (.d 3 14 17))
(.leaf (.d 3 14 18)))))))
(.branch 2299
(.branch 2293
(.branch 2290
(.branch 2289
(.leaf (.d 3 14 19))
(.leaf (.d 3 14 20)))
(.branch 2291
(.leaf (.d 3 14 21))
(.branch 2292
(.leaf (.d 4 14 15))
(.leaf (.d 4 14 16)))))
(.branch 2296
(.branch 2294
(.leaf (.d 4 14 17))
(.branch 2295
(.leaf (.d 4 14 18))
(.leaf (.d 4 14 19))))
(.branch 2297
(.leaf (.d 4 14 20))
(.branch 2298
(.leaf (.d 4 14 21))
(.leaf (.d 5 14 15))))))
(.branch 2304
(.branch 2301
(.branch 2300
(.leaf (.d 5 14 16))
(.leaf (.d 5 14 17)))
(.branch 2302
(.leaf (.d 5 14 18))
(.branch 2303
(.leaf (.d 5 14 19))
(.leaf (.d 5 14 20)))))
(.branch 2307
(.branch 2305
(.leaf (.d 5 14 21))
(.branch 2306
(.leaf (.d 6 14 15))
(.leaf (.d 6 14 16))))
(.branch 2308
(.leaf (.d 6 14 17))
(.branch 2309
(.leaf (.d 6 14 18))
(.leaf (.d 6 14 19)))))))))
(.branch 2353
(.branch 2331
(.branch 2320
(.branch 2315
(.branch 2312
(.branch 2311
(.leaf (.d 6 14 20))
(.leaf (.d 6 14 21)))
(.branch 2313
(.leaf (.d 7 14 15))
(.branch 2314
(.leaf (.d 7 14 16))
(.leaf (.d 7 14 17)))))
(.branch 2317
(.branch 2316
(.leaf (.d 7 14 18))
(.leaf (.d 7 14 19)))
(.branch 2318
(.leaf (.d 7 14 20))
(.branch 2319
(.leaf (.d 7 14 21))
(.leaf (.d 8 14 15))))))
(.branch 2325
(.branch 2322
(.branch 2321
(.leaf (.d 8 14 16))
(.leaf (.d 8 14 17)))
(.branch 2323
(.leaf (.d 8 14 18))
(.branch 2324
(.leaf (.d 8 14 19))
(.leaf (.d 8 14 20)))))
(.branch 2328
(.branch 2326
(.leaf (.d 8 14 21))
(.branch 2327
(.leaf (.d 9 14 15))
(.leaf (.d 9 14 16))))
(.branch 2329
(.leaf (.d 9 14 17))
(.branch 2330
(.leaf (.d 9 14 18))
(.leaf (.d 9 14 19)))))))
(.branch 2342
(.branch 2336
(.branch 2333
(.branch 2332
(.leaf (.d 9 14 20))
(.leaf (.d 9 14 21)))
(.branch 2334
(.leaf (.d 10 14 15))
(.branch 2335
(.leaf (.d 10 14 16))
(.leaf (.d 10 14 17)))))
(.branch 2339
(.branch 2337
(.leaf (.d 10 14 18))
(.branch 2338
(.leaf (.d 10 14 19))
(.leaf (.d 10 14 20))))
(.branch 2340
(.leaf (.d 10 14 21))
(.branch 2341
(.leaf (.d 11 14 15))
(.leaf (.d 11 14 16))))))
(.branch 2347
(.branch 2344
(.branch 2343
(.leaf (.d 11 14 17))
(.leaf (.d 11 14 18)))
(.branch 2345
(.leaf (.d 11 14 19))
(.branch 2346
(.leaf (.d 11 14 20))
(.leaf (.d 11 14 21)))))
(.branch 2350
(.branch 2348
(.leaf (.d 12 14 15))
(.branch 2349
(.leaf (.d 12 14 16))
(.leaf (.d 12 14 17))))
(.branch 2351
(.leaf (.d 12 14 18))
(.branch 2352
(.leaf (.d 12 14 19))
(.leaf (.d 12 14 20))))))))
(.branch 2374
(.branch 2363
(.branch 2358
(.branch 2355
(.branch 2354
(.leaf (.d 12 14 21))
(.leaf (.d 13 14 15)))
(.branch 2356
(.leaf (.d 13 14 16))
(.branch 2357
(.leaf (.d 13 14 17))
(.leaf (.d 13 14 18)))))
(.branch 2360
(.branch 2359
(.leaf (.d 13 14 19))
(.leaf (.d 13 14 20)))
(.branch 2361
(.leaf (.d 13 14 21))
(.branch 2362
(.leaf (.d 14 14 15))
(.leaf (.d 14 14 16))))))
(.branch 2368
(.branch 2365
(.branch 2364
(.leaf (.d 14 14 17))
(.leaf (.d 14 14 18)))
(.branch 2366
(.leaf (.d 14 14 19))
(.branch 2367
(.leaf (.d 14 14 20))
(.leaf (.d 14 14 21)))))
(.branch 2371
(.branch 2369
(.leaf (.d 0 15 16))
(.branch 2370
(.leaf (.d 0 15 17))
(.leaf (.d 0 15 18))))
(.branch 2372
(.leaf (.d 0 15 19))
(.branch 2373
(.leaf (.d 0 15 20))
(.leaf (.d 0 15 21)))))))
(.branch 2385
(.branch 2379
(.branch 2376
(.branch 2375
(.leaf (.d 1 15 16))
(.leaf (.d 1 15 17)))
(.branch 2377
(.leaf (.d 1 15 18))
(.branch 2378
(.leaf (.d 1 15 19))
(.leaf (.d 1 15 20)))))
(.branch 2382
(.branch 2380
(.leaf (.d 1 15 21))
(.branch 2381
(.leaf (.d 2 15 16))
(.leaf (.d 2 15 17))))
(.branch 2383
(.leaf (.d 2 15 18))
(.branch 2384
(.leaf (.d 2 15 19))
(.leaf (.d 2 15 20))))))
(.branch 2390
(.branch 2387
(.branch 2386
(.leaf (.d 2 15 21))
(.leaf (.d 3 15 16)))
(.branch 2388
(.leaf (.d 3 15 17))
(.branch 2389
(.leaf (.d 3 15 18))
(.leaf (.d 3 15 19)))))
(.branch 2393
(.branch 2391
(.leaf (.d 3 15 20))
(.branch 2392
(.leaf (.d 3 15 21))
(.leaf (.d 4 15 16))))
(.branch 2394
(.leaf (.d 4 15 17))
(.branch 2395
(.leaf (.d 4 15 18))
(.leaf (.d 4 15 19)))))))))))
(.branch 2567
(.branch 2481
(.branch 2438
(.branch 2417
(.branch 2406
(.branch 2401
(.branch 2398
(.branch 2397
(.leaf (.d 4 15 20))
(.leaf (.d 4 15 21)))
(.branch 2399
(.leaf (.d 5 15 16))
(.branch 2400
(.leaf (.d 5 15 17))
(.leaf (.d 5 15 18)))))
(.branch 2403
(.branch 2402
(.leaf (.d 5 15 19))
(.leaf (.d 5 15 20)))
(.branch 2404
(.leaf (.d 5 15 21))
(.branch 2405
(.leaf (.d 6 15 16))
(.leaf (.d 6 15 17))))))
(.branch 2411
(.branch 2408
(.branch 2407
(.leaf (.d 6 15 18))
(.leaf (.d 6 15 19)))
(.branch 2409
(.leaf (.d 6 15 20))
(.branch 2410
(.leaf (.d 6 15 21))
(.leaf (.d 7 15 16)))))
(.branch 2414
(.branch 2412
(.leaf (.d 7 15 17))
(.branch 2413
(.leaf (.d 7 15 18))
(.leaf (.d 7 15 19))))
(.branch 2415
(.leaf (.d 7 15 20))
(.branch 2416
(.leaf (.d 7 15 21))
(.leaf (.d 8 15 16)))))))
(.branch 2427
(.branch 2422
(.branch 2419
(.branch 2418
(.leaf (.d 8 15 17))
(.leaf (.d 8 15 18)))
(.branch 2420
(.leaf (.d 8 15 19))
(.branch 2421
(.leaf (.d 8 15 20))
(.leaf (.d 8 15 21)))))
(.branch 2424
(.branch 2423
(.leaf (.d 9 15 16))
(.leaf (.d 9 15 17)))
(.branch 2425
(.leaf (.d 9 15 18))
(.branch 2426
(.leaf (.d 9 15 19))
(.leaf (.d 9 15 20))))))
(.branch 2432
(.branch 2429
(.branch 2428
(.leaf (.d 9 15 21))
(.leaf (.d 10 15 16)))
(.branch 2430
(.leaf (.d 10 15 17))
(.branch 2431
(.leaf (.d 10 15 18))
(.leaf (.d 10 15 19)))))
(.branch 2435
(.branch 2433
(.leaf (.d 10 15 20))
(.branch 2434
(.leaf (.d 10 15 21))
(.leaf (.d 11 15 16))))
(.branch 2436
(.leaf (.d 11 15 17))
(.branch 2437
(.leaf (.d 11 15 18))
(.leaf (.d 11 15 19))))))))
(.branch 2459
(.branch 2448
(.branch 2443
(.branch 2440
(.branch 2439
(.leaf (.d 11 15 20))
(.leaf (.d 11 15 21)))
(.branch 2441
(.leaf (.d 12 15 16))
(.branch 2442
(.leaf (.d 12 15 17))
(.leaf (.d 12 15 18)))))
(.branch 2445
(.branch 2444
(.leaf (.d 12 15 19))
(.leaf (.d 12 15 20)))
(.branch 2446
(.leaf (.d 12 15 21))
(.branch 2447
(.leaf (.d 13 15 16))
(.leaf (.d 13 15 17))))))
(.branch 2453
(.branch 2450
(.branch 2449
(.leaf (.d 13 15 18))
(.leaf (.d 13 15 19)))
(.branch 2451
(.leaf (.d 13 15 20))
(.branch 2452
(.leaf (.d 13 15 21))
(.leaf (.d 14 15 16)))))
(.branch 2456
(.branch 2454
(.leaf (.d 14 15 17))
(.branch 2455
(.leaf (.d 14 15 18))
(.leaf (.d 14 15 19))))
(.branch 2457
(.leaf (.d 14 15 20))
(.branch 2458
(.leaf (.d 14 15 21))
(.leaf (.d 15 15 16)))))))
(.branch 2470
(.branch 2464
(.branch 2461
(.branch 2460
(.leaf (.d 15 15 17))
(.leaf (.d 15 15 18)))
(.branch 2462
(.leaf (.d 15 15 19))
(.branch 2463
(.leaf (.d 15 15 20))
(.leaf (.d 15 15 21)))))
(.branch 2467
(.branch 2465
(.leaf (.d 0 16 17))
(.branch 2466
(.leaf (.d 0 16 18))
(.leaf (.d 0 16 19))))
(.branch 2468
(.leaf (.d 0 16 20))
(.branch 2469
(.leaf (.d 0 16 21))
(.leaf (.d 1 16 17))))))
(.branch 2475
(.branch 2472
(.branch 2471
(.leaf (.d 1 16 18))
(.leaf (.d 1 16 19)))
(.branch 2473
(.leaf (.d 1 16 20))
(.branch 2474
(.leaf (.d 1 16 21))
(.leaf (.d 2 16 17)))))
(.branch 2478
(.branch 2476
(.leaf (.d 2 16 18))
(.branch 2477
(.leaf (.d 2 16 19))
(.leaf (.d 2 16 20))))
(.branch 2479
(.leaf (.d 2 16 21))
(.branch 2480
(.leaf (.d 3 16 17))
(.leaf (.d 3 16 18)))))))))
(.branch 2524
(.branch 2502
(.branch 2491
(.branch 2486
(.branch 2483
(.branch 2482
(.leaf (.d 3 16 19))
(.leaf (.d 3 16 20)))
(.branch 2484
(.leaf (.d 3 16 21))
(.branch 2485
(.leaf (.d 4 16 17))
(.leaf (.d 4 16 18)))))
(.branch 2488
(.branch 2487
(.leaf (.d 4 16 19))
(.leaf (.d 4 16 20)))
(.branch 2489
(.leaf (.d 4 16 21))
(.branch 2490
(.leaf (.d 5 16 17))
(.leaf (.d 5 16 18))))))
(.branch 2496
(.branch 2493
(.branch 2492
(.leaf (.d 5 16 19))
(.leaf (.d 5 16 20)))
(.branch 2494
(.leaf (.d 5 16 21))
(.branch 2495
(.leaf (.d 6 16 17))
(.leaf (.d 6 16 18)))))
(.branch 2499
(.branch 2497
(.leaf (.d 6 16 19))
(.branch 2498
(.leaf (.d 6 16 20))
(.leaf (.d 6 16 21))))
(.branch 2500
(.leaf (.d 7 16 17))
(.branch 2501
(.leaf (.d 7 16 18))
(.leaf (.d 7 16 19)))))))
(.branch 2513
(.branch 2507
(.branch 2504
(.branch 2503
(.leaf (.d 7 16 20))
(.leaf (.d 7 16 21)))
(.branch 2505
(.leaf (.d 8 16 17))
(.branch 2506
(.leaf (.d 8 16 18))
(.leaf (.d 8 16 19)))))
(.branch 2510
(.branch 2508
(.leaf (.d 8 16 20))
(.branch 2509
(.leaf (.d 8 16 21))
(.leaf (.d 9 16 17))))
(.branch 2511
(.leaf (.d 9 16 18))
(.branch 2512
(.leaf (.d 9 16 19))
(.leaf (.d 9 16 20))))))
(.branch 2518
(.branch 2515
(.branch 2514
(.leaf (.d 9 16 21))
(.leaf (.d 10 16 17)))
(.branch 2516
(.leaf (.d 10 16 18))
(.branch 2517
(.leaf (.d 10 16 19))
(.leaf (.d 10 16 20)))))
(.branch 2521
(.branch 2519
(.leaf (.d 10 16 21))
(.branch 2520
(.leaf (.d 11 16 17))
(.leaf (.d 11 16 18))))
(.branch 2522
(.leaf (.d 11 16 19))
(.branch 2523
(.leaf (.d 11 16 20))
(.leaf (.d 11 16 21))))))))
(.branch 2545
(.branch 2534
(.branch 2529
(.branch 2526
(.branch 2525
(.leaf (.d 12 16 17))
(.leaf (.d 12 16 18)))
(.branch 2527
(.leaf (.d 12 16 19))
(.branch 2528
(.leaf (.d 12 16 20))
(.leaf (.d 12 16 21)))))
(.branch 2531
(.branch 2530
(.leaf (.d 13 16 17))
(.leaf (.d 13 16 18)))
(.branch 2532
(.leaf (.d 13 16 19))
(.branch 2533
(.leaf (.d 13 16 20))
(.leaf (.d 13 16 21))))))
(.branch 2539
(.branch 2536
(.branch 2535
(.leaf (.d 14 16 17))
(.leaf (.d 14 16 18)))
(.branch 2537
(.leaf (.d 14 16 19))
(.branch 2538
(.leaf (.d 14 16 20))
(.leaf (.d 14 16 21)))))
(.branch 2542
(.branch 2540
(.leaf (.d 15 16 17))
(.branch 2541
(.leaf (.d 15 16 18))
(.leaf (.d 15 16 19))))
(.branch 2543
(.leaf (.d 15 16 20))
(.branch 2544
(.leaf (.d 15 16 21))
(.leaf (.d 16 16 17)))))))
(.branch 2556
(.branch 2550
(.branch 2547
(.branch 2546
(.leaf (.d 16 16 18))
(.leaf (.d 16 16 19)))
(.branch 2548
(.leaf (.d 16 16 20))
(.branch 2549
(.leaf (.d 16 16 21))
(.leaf (.d 0 17 18)))))
(.branch 2553
(.branch 2551
(.leaf (.d 0 17 19))
(.branch 2552
(.leaf (.d 0 17 20))
(.leaf (.d 0 17 21))))
(.branch 2554
(.leaf (.d 1 17 18))
(.branch 2555
(.leaf (.d 1 17 19))
(.leaf (.d 1 17 20))))))
(.branch 2561
(.branch 2558
(.branch 2557
(.leaf (.d 1 17 21))
(.leaf (.d 2 17 18)))
(.branch 2559
(.leaf (.d 2 17 19))
(.branch 2560
(.leaf (.d 2 17 20))
(.leaf (.d 2 17 21)))))
(.branch 2564
(.branch 2562
(.leaf (.d 3 17 18))
(.branch 2563
(.leaf (.d 3 17 19))
(.leaf (.d 3 17 20))))
(.branch 2565
(.leaf (.d 3 17 21))
(.branch 2566
(.leaf (.d 4 17 18))
(.leaf (.d 4 17 19))))))))))
(.branch 2653
(.branch 2610
(.branch 2588
(.branch 2577
(.branch 2572
(.branch 2569
(.branch 2568
(.leaf (.d 4 17 20))
(.leaf (.d 4 17 21)))
(.branch 2570
(.leaf (.d 5 17 18))
(.branch 2571
(.leaf (.d 5 17 19))
(.leaf (.d 5 17 20)))))
(.branch 2574
(.branch 2573
(.leaf (.d 5 17 21))
(.leaf (.d 6 17 18)))
(.branch 2575
(.leaf (.d 6 17 19))
(.branch 2576
(.leaf (.d 6 17 20))
(.leaf (.d 6 17 21))))))
(.branch 2582
(.branch 2579
(.branch 2578
(.leaf (.d 7 17 18))
(.leaf (.d 7 17 19)))
(.branch 2580
(.leaf (.d 7 17 20))
(.branch 2581
(.leaf (.d 7 17 21))
(.leaf (.d 8 17 18)))))
(.branch 2585
(.branch 2583
(.leaf (.d 8 17 19))
(.branch 2584
(.leaf (.d 8 17 20))
(.leaf (.d 8 17 21))))
(.branch 2586
(.leaf (.d 9 17 18))
(.branch 2587
(.leaf (.d 9 17 19))
(.leaf (.d 9 17 20)))))))
(.branch 2599
(.branch 2593
(.branch 2590
(.branch 2589
(.leaf (.d 9 17 21))
(.leaf (.d 10 17 18)))
(.branch 2591
(.leaf (.d 10 17 19))
(.branch 2592
(.leaf (.d 10 17 20))
(.leaf (.d 10 17 21)))))
(.branch 2596
(.branch 2594
(.leaf (.d 11 17 18))
(.branch 2595
(.leaf (.d 11 17 19))
(.leaf (.d 11 17 20))))
(.branch 2597
(.leaf (.d 11 17 21))
(.branch 2598
(.leaf (.d 12 17 18))
(.leaf (.d 12 17 19))))))
(.branch 2604
(.branch 2601
(.branch 2600
(.leaf (.d 12 17 20))
(.leaf (.d 12 17 21)))
(.branch 2602
(.leaf (.d 13 17 18))
(.branch 2603
(.leaf (.d 13 17 19))
(.leaf (.d 13 17 20)))))
(.branch 2607
(.branch 2605
(.leaf (.d 13 17 21))
(.branch 2606
(.leaf (.d 14 17 18))
(.leaf (.d 14 17 19))))
(.branch 2608
(.leaf (.d 14 17 20))
(.branch 2609
(.leaf (.d 14 17 21))
(.leaf (.d 15 17 18))))))))
(.branch 2631
(.branch 2620
(.branch 2615
(.branch 2612
(.branch 2611
(.leaf (.d 15 17 19))
(.leaf (.d 15 17 20)))
(.branch 2613
(.leaf (.d 15 17 21))
(.branch 2614
(.leaf (.d 16 17 18))
(.leaf (.d 16 17 19)))))
(.branch 2617
(.branch 2616
(.leaf (.d 16 17 20))
(.leaf (.d 16 17 21)))
(.branch 2618
(.leaf (.d 17 17 18))
(.branch 2619
(.leaf (.d 17 17 19))
(.leaf (.d 17 17 20))))))
(.branch 2625
(.branch 2622
(.branch 2621
(.leaf (.d 17 17 21))
(.leaf (.d 0 18 19)))
(.branch 2623
(.leaf (.d 0 18 20))
(.branch 2624
(.leaf (.d 0 18 21))
(.leaf (.d 1 18 19)))))
(.branch 2628
(.branch 2626
(.leaf (.d 1 18 20))
(.branch 2627
(.leaf (.d 1 18 21))
(.leaf (.d 2 18 19))))
(.branch 2629
(.leaf (.d 2 18 20))
(.branch 2630
(.leaf (.d 2 18 21))
(.leaf (.d 3 18 19)))))))
(.branch 2642
(.branch 2636
(.branch 2633
(.branch 2632
(.leaf (.d 3 18 20))
(.leaf (.d 3 18 21)))
(.branch 2634
(.leaf (.d 4 18 19))
(.branch 2635
(.leaf (.d 4 18 20))
(.leaf (.d 4 18 21)))))
(.branch 2639
(.branch 2637
(.leaf (.d 5 18 19))
(.branch 2638
(.leaf (.d 5 18 20))
(.leaf (.d 5 18 21))))
(.branch 2640
(.leaf (.d 6 18 19))
(.branch 2641
(.leaf (.d 6 18 20))
(.leaf (.d 6 18 21))))))
(.branch 2647
(.branch 2644
(.branch 2643
(.leaf (.d 7 18 19))
(.leaf (.d 7 18 20)))
(.branch 2645
(.leaf (.d 7 18 21))
(.branch 2646
(.leaf (.d 8 18 19))
(.leaf (.d 8 18 20)))))
(.branch 2650
(.branch 2648
(.leaf (.d 8 18 21))
(.branch 2649
(.leaf (.d 9 18 19))
(.leaf (.d 9 18 20))))
(.branch 2651
(.leaf (.d 9 18 21))
(.branch 2652
(.leaf (.d 10 18 19))
(.leaf (.d 10 18 20)))))))))
(.branch 2696
(.branch 2674
(.branch 2663
(.branch 2658
(.branch 2655
(.branch 2654
(.leaf (.d 10 18 21))
(.leaf (.d 11 18 19)))
(.branch 2656
(.leaf (.d 11 18 20))
(.branch 2657
(.leaf (.d 11 18 21))
(.leaf (.d 12 18 19)))))
(.branch 2660
(.branch 2659
(.leaf (.d 12 18 20))
(.leaf (.d 12 18 21)))
(.branch 2661
(.leaf (.d 13 18 19))
(.branch 2662
(.leaf (.d 13 18 20))
(.leaf (.d 13 18 21))))))
(.branch 2668
(.branch 2665
(.branch 2664
(.leaf (.d 14 18 19))
(.leaf (.d 14 18 20)))
(.branch 2666
(.leaf (.d 14 18 21))
(.branch 2667
(.leaf (.d 15 18 19))
(.leaf (.d 15 18 20)))))
(.branch 2671
(.branch 2669
(.leaf (.d 15 18 21))
(.branch 2670
(.leaf (.d 16 18 19))
(.leaf (.d 16 18 20))))
(.branch 2672
(.leaf (.d 16 18 21))
(.branch 2673
(.leaf (.d 17 18 19))
(.leaf (.d 17 18 20)))))))
(.branch 2685
(.branch 2679
(.branch 2676
(.branch 2675
(.leaf (.d 17 18 21))
(.leaf (.d 18 18 19)))
(.branch 2677
(.leaf (.d 18 18 20))
(.branch 2678
(.leaf (.d 18 18 21))
(.leaf (.d 0 19 20)))))
(.branch 2682
(.branch 2680
(.leaf (.d 0 19 21))
(.branch 2681
(.leaf (.d 1 19 20))
(.leaf (.d 1 19 21))))
(.branch 2683
(.leaf (.d 2 19 20))
(.branch 2684
(.leaf (.d 2 19 21))
(.leaf (.d 3 19 20))))))
(.branch 2690
(.branch 2687
(.branch 2686
(.leaf (.d 3 19 21))
(.leaf (.d 4 19 20)))
(.branch 2688
(.leaf (.d 4 19 21))
(.branch 2689
(.leaf (.d 5 19 20))
(.leaf (.d 5 19 21)))))
(.branch 2693
(.branch 2691
(.leaf (.d 6 19 20))
(.branch 2692
(.leaf (.d 6 19 21))
(.leaf (.d 7 19 20))))
(.branch 2694
(.leaf (.d 7 19 21))
(.branch 2695
(.leaf (.d 8 19 20))
(.leaf (.d 8 19 21))))))))
(.branch 2717
(.branch 2706
(.branch 2701
(.branch 2698
(.branch 2697
(.leaf (.d 9 19 20))
(.leaf (.d 9 19 21)))
(.branch 2699
(.leaf (.d 10 19 20))
(.branch 2700
(.leaf (.d 10 19 21))
(.leaf (.d 11 19 20)))))
(.branch 2703
(.branch 2702
(.leaf (.d 11 19 21))
(.leaf (.d 12 19 20)))
(.branch 2704
(.leaf (.d 12 19 21))
(.branch 2705
(.leaf (.d 13 19 20))
(.leaf (.d 13 19 21))))))
(.branch 2711
(.branch 2708
(.branch 2707
(.leaf (.d 14 19 20))
(.leaf (.d 14 19 21)))
(.branch 2709
(.leaf (.d 15 19 20))
(.branch 2710
(.leaf (.d 15 19 21))
(.leaf (.d 16 19 20)))))
(.branch 2714
(.branch 2712
(.leaf (.d 16 19 21))
(.branch 2713
(.leaf (.d 17 19 20))
(.leaf (.d 17 19 21))))
(.branch 2715
(.leaf (.d 18 19 20))
(.branch 2716
(.leaf (.d 18 19 21))
(.leaf (.d 19 19 20)))))))
(.branch 2728
(.branch 2722
(.branch 2719
(.branch 2718
(.leaf (.d 19 19 21))
(.leaf (.d 0 20 21)))
(.branch 2720
(.leaf (.d 1 20 21))
(.branch 2721
(.leaf (.d 2 20 21))
(.leaf (.d 3 20 21)))))
(.branch 2725
(.branch 2723
(.leaf (.d 4 20 21))
(.branch 2724
(.leaf (.d 5 20 21))
(.leaf (.d 6 20 21))))
(.branch 2726
(.leaf (.d 7 20 21))
(.branch 2727
(.leaf (.d 8 20 21))
(.leaf (.d 9 20 21))))))
(.branch 2733
(.branch 2730
(.branch 2729
(.leaf (.d 10 20 21))
(.leaf (.d 11 20 21)))
(.branch 2731
(.leaf (.d 12 20 21))
(.branch 2732
(.leaf (.d 13 20 21))
(.leaf (.d 14 20 21)))))
(.branch 2736
(.branch 2734
(.leaf (.d 15 20 21))
(.branch 2735
(.leaf (.d 16 20 21))
(.leaf (.d 17 20 21))))
(.branch 2737
(.leaf (.d 18 20 21))
(.branch 2738
(.leaf (.d 19 20 21))
(.leaf (.d 20 20 21))))))))))))))
def coordOfIndex (k:ℕ):Coord 22:=coordinateTable.get k
end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


