-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0512To0767
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_Steps0512To0767
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:52:21.548405+00:00
-- url     : https://prove2.me/theorems/27bb639a-9888-4b47-9da4-a8501f52099c
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / Steps0512To0767
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps0512To0767` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated from ssa-witness.json.gz. All certificates use the Lean kernel.
--   Eight consecutive 32-step certificates share one module and adjacent snapshots.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps0512To0767

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSASparseIndices
import Definitions.Def_CSL_Circuit_Local_SSAAdjacentChecks
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows

/-! Generated from ssa-witness.json.gz. All certificates use the Lean kernel.
Eight consecutive 32-step certificates share one module and adjacent snapshots. -/

namespace CSL.Construction.FiniteSSA.Verified.Block016
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def before (i : Nat) : Nat := (if i < 388 then (if i < 321 then (if i < 269 then (if i < 243 then (if i < 233 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 826))) else (if i < 224 then (i + 827) else (if i < 232 then (i + 551) else (i + 782)))) else (if i < 240 then (if i < 234 then (i + 551) else (if i < 235 then (i + 786) else (i + 551))) else (if i < 241 then (i + 776) else (if i < 242 then (i + 551) else (i + 776))))) else (if i < 254 then (if i < 247 then (if i < 244 then (i + 780) else (if i < 246 then (i + 549) else (i + 808))) else (if i < 252 then (i + 549) else (if i < 253 then (i + 800) else (i + 803)))) else (if i < 264 then (if i < 256 then (i + 547) else (if i < 257 then (i + 827) else (i + 547))) else (if i < 266 then (if i < 265 then (i + 855) else (i + 856)) else (if i < 268 then (i + 547) else (i + 883)))))) else (if i < 299 then (if i < 281 then (if i < 273 then (if i < 270 then (i + 886) else (if i < 272 then (i + 547) else (i + 809))) else (if i < 279 then (i + 547) else (if i < 280 then (i + 878) else (i + 837)))) else (if i < 287 then (if i < 282 then (i + 842) else (if i < 286 then (i + 547) else (i + 809))) else (if i < 297 then (if i < 296 then (i + 547) else (i + 833)) else (if i < 298 then (i + 547) else (i + 865))))) else (if i < 313 then (if i < 309 then (if i < 300 then (i + 866) else (if i < 308 then (i + 547) else (i + 785))) else (if i < 310 then (i + 792) else (if i < 312 then (i + 547) else (i + 823)))) else (if i < 316 then (if i < 314 then (i + 547) else (if i < 315 then (i + 855) else (i + 856))) else (if i < 319 then (if i < 318 then (i + 547) else (i + 709)) else (if i < 320 then (i + 547) else (i + 716))))))) else (if i < 352 then (if i < 337 then (if i < 327 then (if i < 324 then (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721))) else (if i < 325 then (i + 701) else (if i < 326 then (i + 706) else (i + 781)))) else (if i < 330 then (if i < 328 then (i + 545) else (if i < 329 then (i + 813) else (i + 814))) else (if i < 334 then (i + 543) else (if i < 336 then (i + 1) else (i + 706))))) else (if i < 344 then (if i < 340 then (if i < 338 then (i + 709) else (if i < 339 then (i + 767) else (i + 774))) else (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 541)))) else (if i < 348 then (if i < 345 then (i + 685) else (if i < 347 then (i + 541) else (i + 800))) else (if i < 350 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 351 then (i + 761) else (i + 764)))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (i + 541) else (if i < 355 then (i + 705) else (i + 707))) else (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705)))) else (if i < 364 then (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 539))) else (if i < 366 then (if i < 365 then (i + 781) else (i + 539)) else (if i < 367 then (i + 706) else (i + 709))))) else (if i < 376 then (if i < 372 then (if i < 369 then (i + 537) else (if i < 370 then (i + 780) else (i + 537))) else (if i < 373 then (i + 702) else (if i < 375 then (i + 537) else (i + 693)))) else (if i < 381 then (if i < 377 then (i + 733) else (if i < 380 then (i + 537) else (i + 686))) else (if i < 385 then (if i < 384 then (i + 537) else (i + 747)) else (if i < 387 then (i + 537) else (i + 712)))))))) else (if i < 510 then (if i < 446 then (if i < 420 then (if i < 403 then (if i < 400 then (if i < 397 then (i + 537) else (if i < 398 then (i + 776) else (i + 537))) else (if i < 401 then (i + 733) else (if i < 402 then (i + 737) else (i + 695)))) else (if i < 407 then (if i < 404 then (i + 700) else (if i < 406 then (i + 535) else (i + 761))) else (if i < 417 then (i + 535) else (if i < 418 then (i + 710) else (i + 535))))) else (if i < 430 then (if i < 426 then (if i < 421 then (i + 667) else (if i < 422 then (i + 670) else (i + 535))) else (if i < 427 then (i + 727) else (if i < 428 then (i + 734) else (i + 535)))) else (if i < 433 then (if i < 431 then (i + 655) else (if i < 432 then (i + 658) else (i + 693))) else (if i < 443 then (if i < 442 then (i + 535) else (i + 717)) else (if i < 444 then (i + 535) else (i + 1)))))) else (if i < 495 then (if i < 487 then (if i < 483 then (if i < 481 then (i + 533) else (if i < 482 then (i + 534) else (i + 535))) else (if i < 484 then (i + 536) else (if i < 486 then (i + 537) else (i + 538)))) else (if i < 490 then (if i < 488 then (i + 539) else (if i < 489 then (i + 540) else (i + 541))) else (if i < 493 then (if i < 492 then (i + 542) else (i + 543)) else (if i < 494 then (i + 544) else (i + 545))))) else (if i < 501 then (if i < 498 then (if i < 496 then (i + 546) else (if i < 497 then (i + 547) else (i + 548))) else (if i < 499 then (i + 549) else (if i < 500 then (i + 550) else (i + 551)))) else (if i < 505 then (if i < 502 then (i + 552) else (if i < 503 then (i + 553) else (i + 554))) else (if i < 508 then (if i < 507 then (i + 555) else (i + 556)) else (if i < 509 then (i + 557) else (i + 558))))))) else (if i < 537 then (if i < 524 then (if i < 517 then (if i < 513 then (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561))) else (if i < 514 then (i + 562) else (if i < 515 then (i + 563) else (i + 564)))) else (if i < 520 then (if i < 518 then (i + 565) else (if i < 519 then (i + 566) else (i + 567))) else (if i < 522 then (if i < 521 then (i + 568) else (i + 569)) else (if i < 523 then (i + 570) else (i + 571))))) else (if i < 530 then (if i < 527 then (if i < 525 then (i + 572) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 528 then (i + 575) else (if i < 529 then (i + 576) else (i + 577)))) else (if i < 533 then (if i < 531 then (i + 578) else (if i < 532 then (i + 579) else (i + 580))) else (if i < 535 then (if i < 534 then (i + 581) else (i + 582)) else (if i < 536 then (i + 583) else (i + 584)))))) else (if i < 552 then (if i < 543 then (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590)))) else (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 550 then (if i < 549 then (i + 594) else (i + 595)) else (if i < 551 then (i + 596) else (i + 597))))) else (if i < 558 then (if i < 555 then (if i < 553 then (i + 598) else (if i < 554 then (i + 599) else (i + 600))) else (if i < 556 then (i + 601) else (if i < 557 then (i + 602) else (i + 603)))) else (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 563 then (if i < 562 then (i + 607) else (i + 608)) else (if i < 564 then (i + 609) else (i + 1)))))))))

def after (i : Nat) : Nat := (if i < 400 then (if i < 321 then (if i < 271 then (if i < 246 then (if i < 234 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 826))) else (if i < 232 then (if i < 224 then (i + 827) else (i + 551)) else (if i < 233 then (i + 782) else (i + 551)))) else (if i < 241 then (if i < 235 then (i + 786) else (if i < 240 then (i + 551) else (i + 776))) else (if i < 243 then (if i < 242 then (i + 551) else (i + 776)) else (if i < 244 then (i + 780) else (i + 549))))) else (if i < 260 then (if i < 253 then (if i < 247 then (i + 808) else (if i < 252 then (i + 549) else (i + 800))) else (if i < 256 then (if i < 254 then (i + 803) else (i + 547)) else (if i < 257 then (i + 827) else (i + 547)))) else (if i < 266 then (if i < 264 then (if i < 261 then (i + 927) else (i + 547)) else (if i < 265 then (i + 855) else (i + 856))) else (if i < 269 then (if i < 268 then (i + 547) else (i + 883)) else (if i < 270 then (i + 886) else (i + 922)))))) else (if i < 300 then (if i < 286 then (if i < 279 then (if i < 272 then (i + 547) else (if i < 273 then (i + 809) else (i + 547))) else (if i < 281 then (if i < 280 then (i + 878) else (i + 837)) else (if i < 282 then (i + 842) else (i + 547)))) else (if i < 296 then (if i < 292 then (if i < 287 then (i + 809) else (i + 547)) else (if i < 293 then (i + 907) else (i + 547))) else (if i < 298 then (if i < 297 then (i + 833) else (i + 547)) else (if i < 299 then (i + 865) else (i + 866))))) else (if i < 312 then (if i < 304 then (if i < 302 then (i + 547) else (if i < 303 then (i + 895) else (i + 902))) else (if i < 309 then (if i < 308 then (i + 547) else (i + 785)) else (if i < 310 then (i + 792) else (i + 547)))) else (if i < 316 then (if i < 314 then (if i < 313 then (i + 823) else (i + 547)) else (if i < 315 then (i + 855) else (i + 856))) else (if i < 319 then (if i < 318 then (i + 547) else (i + 709)) else (if i < 320 then (i + 547) else (i + 716))))))) else (if i < 357 then (if i < 340 then (if i < 328 then (if i < 324 then (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721))) else (if i < 326 then (if i < 325 then (i + 701) else (i + 706)) else (if i < 327 then (i + 781) else (i + 545)))) else (if i < 336 then (if i < 330 then (if i < 329 then (i + 813) else (i + 814)) else (if i < 334 then (i + 543) else (i + 1))) else (if i < 338 then (if i < 337 then (i + 706) else (i + 709)) else (if i < 339 then (i + 767) else (i + 774))))) else (if i < 348 then (if i < 343 then (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 833))) else (if i < 345 then (if i < 344 then (i + 840) else (i + 685)) else (if i < 347 then (i + 541) else (i + 800)))) else (if i < 352 then (if i < 350 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 351 then (i + 761) else (i + 764))) else (if i < 355 then (if i < 354 then (i + 541) else (i + 705)) else (if i < 356 then (i + 707) else (i + 714)))))) else (if i < 375 then (if i < 365 then (if i < 361 then (if i < 359 then (i + 539) else (if i < 360 then (i + 705) else (i + 539))) else (if i < 363 then (if i < 362 then (i + 717) else (i + 815)) else (if i < 364 then (i + 818) else (i + 781)))) else (if i < 369 then (if i < 367 then (if i < 366 then (i + 539) else (i + 706)) else (if i < 368 then (i + 709) else (i + 537))) else (if i < 372 then (if i < 370 then (i + 780) else (i + 537)) else (if i < 373 then (i + 702) else (i + 537))))) else (if i < 384 then (if i < 378 then (if i < 376 then (i + 693) else (if i < 377 then (i + 733) else (i + 537))) else (if i < 380 then (if i < 379 then (i + 801) else (i + 806)) else (if i < 381 then (i + 686) else (i + 537)))) else (if i < 390 then (if i < 387 then (if i < 385 then (i + 747) else (i + 537)) else (if i < 388 then (i + 712) else (i + 537))) else (if i < 397 then (if i < 391 then (i + 813) else (i + 537)) else (if i < 398 then (i + 776) else (i + 537)))))))) else (if i < 518 then (if i < 483 then (if i < 423 then (if i < 412 then (if i < 403 then (if i < 401 then (i + 733) else (if i < 402 then (i + 737) else (i + 695))) else (if i < 406 then (if i < 404 then (i + 700) else (i + 535)) else (if i < 407 then (i + 761) else (i + 535)))) else (if i < 418 then (if i < 413 then (i + 789) else (if i < 417 then (i + 535) else (i + 710))) else (if i < 421 then (if i < 420 then (i + 535) else (i + 667)) else (if i < 422 then (i + 670) else (i + 767))))) else (if i < 433 then (if i < 428 then (if i < 426 then (i + 535) else (if i < 427 then (i + 727) else (i + 734))) else (if i < 431 then (if i < 430 then (i + 535) else (i + 655)) else (if i < 432 then (i + 658) else (i + 693)))) else (if i < 445 then (if i < 443 then (if i < 442 then (i + 535) else (i + 717)) else (if i < 444 then (i + 535) else (i + 1))) else (if i < 481 then (if i < 446 then (i + 749) else (i + 533)) else (if i < 482 then (i + 534) else (i + 535)))))) else (if i < 500 then (if i < 492 then (if i < 487 then (if i < 484 then (i + 536) else (if i < 486 then (i + 537) else (i + 538))) else (if i < 489 then (if i < 488 then (i + 539) else (i + 540)) else (if i < 490 then (i + 541) else (i + 542)))) else (if i < 496 then (if i < 494 then (if i < 493 then (i + 543) else (i + 544)) else (if i < 495 then (i + 545) else (i + 546))) else (if i < 498 then (if i < 497 then (i + 547) else (i + 548)) else (if i < 499 then (i + 549) else (i + 550))))) else (if i < 509 then (if i < 503 then (if i < 501 then (i + 551) else (if i < 502 then (i + 552) else (i + 553))) else (if i < 507 then (if i < 505 then (i + 554) else (i + 555)) else (if i < 508 then (i + 556) else (i + 557)))) else (if i < 513 then (if i < 511 then (if i < 510 then (i + 558) else (i + 559)) else (if i < 512 then (i + 560) else (i + 561))) else (if i < 515 then (if i < 514 then (i + 562) else (i + 563)) else (if i < 517 then (i + 564) else (i + 565))))))) else (if i < 550 then (if i < 533 then (if i < 525 then (if i < 521 then (if i < 519 then (i + 566) else (if i < 520 then (i + 567) else (i + 568))) else (if i < 523 then (if i < 522 then (i + 569) else (i + 570)) else (if i < 524 then (i + 571) else (i + 572)))) else (if i < 529 then (if i < 527 then (if i < 526 then (i + 573) else (i + 574)) else (if i < 528 then (i + 575) else (i + 576))) else (if i < 531 then (if i < 530 then (i + 577) else (i + 578)) else (if i < 532 then (i + 579) else (i + 580))))) else (if i < 540 then (if i < 536 then (if i < 534 then (i + 581) else (if i < 535 then (i + 582) else (i + 583))) else (if i < 538 then (if i < 537 then (i + 584) else (i + 585)) else (if i < 539 then (i + 586) else (i + 587)))) else (if i < 544 then (if i < 542 then (if i < 541 then (i + 588) else (i + 589)) else (if i < 543 then (i + 590) else (i + 591))) else (if i < 548 then (if i < 546 then (i + 592) else (i + 593)) else (if i < 549 then (i + 594) else (i + 595)))))) else (if i < 565 then (if i < 557 then (if i < 553 then (if i < 551 then (i + 596) else (if i < 552 then (i + 597) else (i + 598))) else (if i < 555 then (if i < 554 then (i + 599) else (i + 600)) else (if i < 556 then (i + 601) else (i + 602)))) else (if i < 561 then (if i < 559 then (if i < 558 then (i + 603) else (i + 604)) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 563 then (if i < 562 then (i + 607) else (i + 608)) else (if i < 564 then (i + 609) else (i + 610))))) else (if i < 572 then (if i < 568 then (if i < 566 then (i + 611) else (if i < 567 then (i + 612) else (i + 613))) else (if i < 570 then (if i < 569 then (i + 614) else (i + 615)) else (if i < 571 then (i + 616) else (i + 617)))) else (if i < 578 then (if i < 575 then (if i < 574 then (i + 618) else (i + 619)) else (if i < 577 then (i + 620) else (i + 621))) else (if i < 580 then (if i < 579 then (i + 622) else (i + 623)) else (if i < 581 then (i + 624) else (i + 1)))))))))

def steps : List Step := [⟨⟨175,564,[397]⟩,1174⟩,
⟨⟨176,342,[332]⟩,1175⟩,
⟨⟨176,565,[342]⟩,1176⟩,
⟨⟨177,362,[333]⟩,1177⟩,
⟨⟨177,566,[362]⟩,1178⟩,
⟨⟨178,378,[51]⟩,1179⟩,
⟨⟨178,567,[378]⟩,1180⟩,
⟨⟨179,363,[55]⟩,1181⟩,
⟨⟨179,568,[363]⟩,1182⟩,
⟨⟨180,343,[71]⟩,1183⟩,
⟨⟨180,569,[343]⟩,1184⟩,
⟨⟨181,379,[64]⟩,1185⟩,
⟨⟨181,570,[379]⟩,1186⟩,
⟨⟨182,260,[22]⟩,1187⟩,
⟨⟨182,571,[260]⟩,1188⟩,
⟨⟨183,422,[17]⟩,1189⟩,
⟨⟨183,572,[422]⟩,1190⟩,
⟨⟨19,573,[261]⟩,1191⟩,
⟨⟨184,270,[92]⟩,1192⟩,
⟨⟨184,574,[270]⟩,1193⟩,
⟨⟨24,445,[271]⟩,1194⟩,
⟨⟨24,575,[445]⟩,1195⟩,
⟨⟨94,576,[423]⟩,1196⟩,
⟨⟨185,302,[33]⟩,1197⟩,
⟨⟨185,577,[302]⟩,1198⟩,
⟨⟨186,292,[77]⟩,1199⟩,
⟨⟨186,578,[292]⟩,1200⟩,
⟨⟨187,412,[293]⟩,1201⟩,
⟨⟨187,579,[412]⟩,1202⟩,
⟨⟨188,390,[38]⟩,1203⟩,
⟨⟨188,580,[390]⟩,1204⟩,
⟨⟨189,303,[87]⟩,1205⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block016

namespace CSL.Construction.FiniteSSA.Verified.Block017
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block016.after

def after (i : Nat) : Nat := (if i < 408 then (if i < 325 then (if i < 279 then (if i < 251 then (if i < 235 then (if i < 224 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (i + 827))) else (if i < 233 then (if i < 232 then (i + 551) else (i + 782)) else (if i < 234 then (i + 551) else (i + 786)))) else (if i < 243 then (if i < 241 then (if i < 240 then (i + 551) else (i + 776)) else (if i < 242 then (i + 551) else (i + 776))) else (if i < 245 then (if i < 244 then (i + 780) else (i + 976)) else (if i < 246 then (i + 549) else (if i < 247 then (i + 808) else (i + 549)))))) else (if i < 264 then (if i < 256 then (if i < 253 then (if i < 252 then (i + 977) else (i + 800)) else (if i < 254 then (i + 803) else (i + 547))) else (if i < 260 then (if i < 257 then (i + 827) else (i + 547)) else (if i < 261 then (i + 927) else (i + 547)))) else (if i < 269 then (if i < 266 then (if i < 265 then (i + 855) else (i + 856)) else (if i < 268 then (i + 547) else (i + 883))) else (if i < 271 then (if i < 270 then (i + 886) else (i + 922)) else (if i < 272 then (i + 547) else (if i < 273 then (i + 809) else (i + 547))))))) else (if i < 303 then (if i < 293 then (if i < 286 then (if i < 281 then (if i < 280 then (i + 878) else (i + 837)) else (if i < 282 then (i + 842) else (i + 547))) else (if i < 291 then (if i < 287 then (i + 809) else (i + 547)) else (if i < 292 then (i + 943) else (i + 907)))) else (if i < 297 then (if i < 295 then (if i < 294 then (i + 547) else (i + 938)) else (if i < 296 then (i + 547) else (i + 833))) else (if i < 299 then (if i < 298 then (i + 547) else (i + 865)) else (if i < 300 then (i + 866) else (if i < 302 then (i + 547) else (i + 895)))))) else (if i < 315 then (if i < 310 then (if i < 308 then (if i < 304 then (i + 902) else (i + 547)) else (if i < 309 then (i + 785) else (i + 792))) else (if i < 313 then (if i < 312 then (i + 547) else (i + 823)) else (if i < 314 then (i + 547) else (i + 855)))) else (if i < 320 then (if i < 318 then (if i < 316 then (i + 856) else (i + 547)) else (if i < 319 then (i + 709) else (i + 547))) else (if i < 322 then (if i < 321 then (i + 716) else (i + 717)) else (if i < 323 then (i + 547) else (if i < 324 then (i + 721) else (i + 701)))))))) else (if i < 362 then (if i < 343 then (if i < 334 then (if i < 329 then (if i < 327 then (if i < 326 then (i + 706) else (i + 781)) else (if i < 328 then (i + 545) else (i + 813))) else (if i < 331 then (if i < 330 then (i + 814) else (i + 881)) else (if i < 332 then (i + 882) else (i + 543)))) else (if i < 338 then (if i < 336 then (if i < 335 then (i + 875) else (i + 880)) else (if i < 337 then (i + 706) else (i + 709))) else (if i < 340 then (if i < 339 then (i + 767) else (i + 774)) else (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 833)))))) else (if i < 352 then (if i < 348 then (if i < 345 then (if i < 344 then (i + 840) else (i + 685)) else (if i < 347 then (i + 541) else (i + 800))) else (if i < 350 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 351 then (i + 761) else (i + 764)))) else (if i < 356 then (if i < 354 then (if i < 353 then (i + 541) else (i + 865)) else (if i < 355 then (i + 705) else (i + 707))) else (if i < 359 then (if i < 357 then (i + 714) else (i + 539)) else (if i < 360 then (i + 705) else (if i < 361 then (i + 539) else (i + 717))))))) else (if i < 381 then (if i < 370 then (if i < 366 then (if i < 364 then (if i < 363 then (i + 815) else (i + 818)) else (if i < 365 then (i + 781) else (i + 539))) else (if i < 368 then (if i < 367 then (i + 706) else (i + 709)) else (if i < 369 then (i + 537) else (i + 780)))) else (if i < 376 then (if i < 373 then (if i < 372 then (i + 537) else (i + 702)) else (if i < 375 then (i + 537) else (i + 693))) else (if i < 378 then (if i < 377 then (i + 733) else (i + 537)) else (if i < 379 then (i + 801) else (if i < 380 then (i + 806) else (i + 686)))))) else (if i < 397 then (if i < 388 then (if i < 385 then (if i < 384 then (i + 537) else (i + 747)) else (if i < 387 then (i + 537) else (i + 712))) else (if i < 391 then (if i < 390 then (i + 537) else (i + 813)) else (if i < 392 then (i + 816) else (i + 537)))) else (if i < 402 then (if i < 400 then (if i < 398 then (i + 776) else (i + 537)) else (if i < 401 then (i + 733) else (i + 737))) else (if i < 404 then (if i < 403 then (i + 695) else (i + 700)) else (if i < 406 then (i + 535) else (if i < 407 then (i + 761) else (i + 535))))))))) else (if i < 526 then (if i < 488 then (if i < 442 then (if i < 422 then (if i < 417 then (if i < 412 then (if i < 409 then (i + 828) else (i + 535)) else (if i < 413 then (i + 789) else (i + 535))) else (if i < 420 then (if i < 418 then (i + 710) else (i + 535)) else (if i < 421 then (i + 667) else (i + 670)))) else (if i < 428 then (if i < 426 then (if i < 423 then (i + 767) else (i + 535)) else (if i < 427 then (i + 727) else (i + 734))) else (if i < 431 then (if i < 430 then (i + 535) else (i + 655)) else (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535)))))) else (if i < 454 then (if i < 446 then (if i < 444 then (if i < 443 then (i + 717) else (i + 535)) else (if i < 445 then (i + 1) else (i + 749))) else (if i < 449 then (if i < 448 then (i + 533) else (i + 774)) else (if i < 450 then (i + 777) else (i + 533)))) else (if i < 482 then (if i < 456 then (if i < 455 then (i + 770) else (i + 775)) else (if i < 481 then (i + 533) else (i + 534))) else (if i < 484 then (if i < 483 then (i + 535) else (i + 536)) else (if i < 486 then (i + 537) else (if i < 487 then (i + 538) else (i + 539))))))) else (if i < 508 then (if i < 497 then (if i < 493 then (if i < 490 then (if i < 489 then (i + 540) else (i + 541)) else (if i < 492 then (i + 542) else (i + 543))) else (if i < 495 then (if i < 494 then (i + 544) else (i + 545)) else (if i < 496 then (i + 546) else (i + 547)))) else (if i < 501 then (if i < 499 then (if i < 498 then (i + 548) else (i + 549)) else (if i < 500 then (i + 550) else (i + 551))) else (if i < 503 then (if i < 502 then (i + 552) else (i + 553)) else (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556)))))) else (if i < 517 then (if i < 512 then (if i < 510 then (if i < 509 then (i + 557) else (i + 558)) else (if i < 511 then (i + 559) else (i + 560))) else (if i < 514 then (if i < 513 then (i + 561) else (i + 562)) else (if i < 515 then (i + 563) else (i + 564)))) else (if i < 521 then (if i < 519 then (if i < 518 then (i + 565) else (i + 566)) else (if i < 520 then (i + 567) else (i + 568))) else (if i < 523 then (if i < 522 then (i + 569) else (i + 570)) else (if i < 524 then (i + 571) else (if i < 525 then (i + 572) else (i + 573)))))))) else (if i < 562 then (if i < 543 then (if i < 534 then (if i < 530 then (if i < 528 then (if i < 527 then (i + 574) else (i + 575)) else (if i < 529 then (i + 576) else (i + 577))) else (if i < 532 then (if i < 531 then (i + 578) else (i + 579)) else (if i < 533 then (i + 580) else (i + 581)))) else (if i < 538 then (if i < 536 then (if i < 535 then (i + 582) else (i + 583)) else (if i < 537 then (i + 584) else (i + 585))) else (if i < 540 then (if i < 539 then (i + 586) else (i + 587)) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590)))))) else (if i < 553 then (if i < 549 then (if i < 546 then (if i < 544 then (i + 591) else (i + 592)) else (if i < 548 then (i + 593) else (i + 594))) else (if i < 551 then (if i < 550 then (i + 595) else (i + 596)) else (if i < 552 then (i + 597) else (i + 598)))) else (if i < 557 then (if i < 555 then (if i < 554 then (i + 599) else (i + 600)) else (if i < 556 then (i + 601) else (i + 602))) else (if i < 559 then (if i < 558 then (i + 603) else (i + 604)) else (if i < 560 then (i + 605) else (if i < 561 then (i + 606) else (i + 607))))))) else (if i < 581 then (if i < 570 then (if i < 566 then (if i < 564 then (if i < 563 then (i + 608) else (i + 609)) else (if i < 565 then (i + 610) else (i + 611))) else (if i < 568 then (if i < 567 then (i + 612) else (i + 613)) else (if i < 569 then (i + 614) else (i + 615)))) else (if i < 575 then (if i < 572 then (if i < 571 then (i + 616) else (i + 617)) else (if i < 574 then (i + 618) else (i + 619))) else (if i < 578 then (if i < 577 then (i + 620) else (i + 621)) else (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624)))))) else (if i < 590 then (if i < 585 then (if i < 583 then (if i < 582 then (i + 625) else (i + 626)) else (if i < 584 then (i + 627) else (i + 628))) else (if i < 588 then (if i < 586 then (i + 629) else (i + 630)) else (if i < 589 then (i + 631) else (i + 632)))) else (if i < 594 then (if i < 592 then (if i < 591 then (i + 633) else (i + 634)) else (if i < 593 then (i + 635) else (i + 636))) else (if i < 596 then (if i < 595 then (i + 637) else (i + 638)) else (if i < 597 then (i + 639) else (if i < 598 then (i + 640) else (i + 1))))))))))

def steps : List Step := [⟨⟨189,581,[303]⟩,1206⟩,
⟨⟨190,391,[413]⟩,1207⟩,
⟨⟨190,582,[391]⟩,1208⟩,
⟨⟨52,334,[50]⟩,1209⟩,
⟨⟨52,583,[334]⟩,1210⟩,
⟨⟨191,330,[352]⟩,1211⟩,
⟨⟨191,584,[330]⟩,1212⟩,
⟨⟨192,331,[67]⟩,1213⟩,
⟨⟨192,585,[331]⟩,1214⟩,
⟨⟨62,335,[60]⟩,1215⟩,
⟨⟨62,586,[335]⟩,1216⟩,
⟨⟨69,587,[370]⟩,1217⟩,
⟨⟨193,353,[371]⟩,1218⟩,
⟨⟨193,588,[353]⟩,1219⟩,
⟨⟨194,244,[13]⟩,1220⟩,
⟨⟨194,589,[244]⟩,1221⟩,
⟨⟨195,448,[10]⟩,1222⟩,
⟨⟨195,590,[448]⟩,1223⟩,
⟨⟨196,454,[245]⟩,1224⟩,
⟨⟨196,591,[454]⟩,1225⟩,
⟨⟨197,449,[250]⟩,1226⟩,
⟨⟨197,592,[449]⟩,1227⟩,
⟨⟨198,251,[107]⟩,1228⟩,
⟨⟨198,593,[251]⟩,1229⟩,
⟨⟨199,455,[104]⟩,1230⟩,
⟨⟨199,594,[455]⟩,1231⟩,
⟨⟨200,294,[290]⟩,1232⟩,
⟨⟨200,595,[294]⟩,1233⟩,
⟨⟨201,291,[83]⟩,1234⟩,
⟨⟨201,596,[291]⟩,1235⟩,
⟨⟨202,408,[32]⟩,1236⟩,
⟨⟨202,597,[408]⟩,1237⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block017

namespace CSL.Construction.FiniteSSA.Verified.Block018
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block017.after

def after (i : Nat) : Nat := (if i < 412 then (if i < 324 then (if i < 274 then (if i < 246 then (if i < 234 then (if i < 224 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (i + 827))) else (if i < 226 then (if i < 225 then (i + 1034) else (i + 1035)) else (if i < 232 then (i + 551) else (if i < 233 then (i + 782) else (i + 551))))) else (if i < 241 then (if i < 236 then (if i < 235 then (i + 786) else (i + 551)) else (if i < 237 then (i + 1020) else (if i < 240 then (i + 551) else (i + 776)))) else (if i < 243 then (if i < 242 then (i + 551) else (i + 776)) else (if i < 244 then (i + 780) else (if i < 245 then (i + 976) else (i + 549)))))) else (if i < 261 then (if i < 253 then (if i < 251 then (if i < 247 then (i + 808) else (i + 549)) else (if i < 252 then (i + 977) else (i + 800))) else (if i < 256 then (if i < 254 then (i + 803) else (i + 547)) else (if i < 257 then (i + 827) else (if i < 260 then (i + 547) else (i + 927))))) else (if i < 269 then (if i < 265 then (if i < 264 then (i + 547) else (i + 855)) else (if i < 266 then (i + 856) else (if i < 268 then (i + 547) else (i + 883)))) else (if i < 271 then (if i < 270 then (i + 886) else (i + 922)) else (if i < 272 then (i + 547) else (if i < 273 then (i + 809) else (i + 547))))))) else (if i < 303 then (if i < 292 then (if i < 281 then (if i < 279 then (if i < 275 then (i + 994) else (i + 547)) else (if i < 280 then (i + 878) else (i + 837))) else (if i < 286 then (if i < 282 then (i + 842) else (i + 547)) else (if i < 287 then (i + 809) else (if i < 291 then (i + 547) else (i + 943))))) else (if i < 297 then (if i < 294 then (if i < 293 then (i + 907) else (i + 547)) else (if i < 295 then (i + 938) else (if i < 296 then (i + 547) else (i + 833)))) else (if i < 299 then (if i < 298 then (i + 547) else (i + 865)) else (if i < 300 then (i + 866) else (if i < 302 then (i + 547) else (i + 895)))))) else (if i < 313 then (if i < 308 then (if i < 305 then (if i < 304 then (i + 902) else (i + 940)) else (if i < 306 then (i + 943) else (i + 547))) else (if i < 310 then (if i < 309 then (i + 785) else (i + 792)) else (if i < 311 then (i + 940) else (if i < 312 then (i + 547) else (i + 823))))) else (if i < 319 then (if i < 315 then (if i < 314 then (i + 547) else (i + 855)) else (if i < 316 then (i + 856) else (if i < 318 then (i + 547) else (i + 709)))) else (if i < 321 then (if i < 320 then (i + 547) else (i + 716)) else (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721)))))))) else (if i < 365 then (if i < 344 then (if i < 334 then (if i < 328 then (if i < 326 then (if i < 325 then (i + 701) else (i + 706)) else (if i < 327 then (i + 781) else (i + 545))) else (if i < 330 then (if i < 329 then (i + 813) else (i + 814)) else (if i < 331 then (i + 881) else (if i < 332 then (i + 882) else (i + 543))))) else (if i < 339 then (if i < 336 then (if i < 335 then (i + 875) else (i + 880)) else (if i < 337 then (i + 706) else (if i < 338 then (i + 709) else (i + 767)))) else (if i < 341 then (if i < 340 then (i + 774) else (i + 541)) else (if i < 342 then (i + 693) else (if i < 343 then (i + 833) else (i + 840)))))) else (if i < 354 then (if i < 349 then (if i < 347 then (if i < 345 then (i + 685) else (i + 541)) else (if i < 348 then (i + 800) else (i + 692))) else (if i < 351 then (if i < 350 then (i + 541) else (i + 761)) else (if i < 352 then (i + 764) else (if i < 353 then (i + 541) else (i + 865))))) else (if i < 360 then (if i < 356 then (if i < 355 then (i + 705) else (i + 707)) else (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705)))) else (if i < 362 then (if i < 361 then (i + 539) else (i + 717)) else (if i < 363 then (i + 815) else (if i < 364 then (i + 818) else (i + 781))))))) else (if i < 389 then (if i < 376 then (if i < 369 then (if i < 367 then (if i < 366 then (i + 539) else (i + 706)) else (if i < 368 then (i + 709) else (i + 537))) else (if i < 372 then (if i < 370 then (i + 780) else (i + 537)) else (if i < 373 then (i + 702) else (if i < 375 then (i + 537) else (i + 693))))) else (if i < 381 then (if i < 378 then (if i < 377 then (i + 733) else (i + 537)) else (if i < 379 then (i + 801) else (if i < 380 then (i + 806) else (i + 686)))) else (if i < 385 then (if i < 384 then (i + 537) else (i + 747)) else (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858)))))) else (if i < 401 then (if i < 395 then (if i < 391 then (if i < 390 then (i + 865) else (i + 813)) else (if i < 392 then (i + 816) else (i + 537))) else (if i < 397 then (if i < 396 then (i + 857) else (i + 537)) else (if i < 398 then (i + 776) else (if i < 400 then (i + 537) else (i + 733))))) else (if i < 406 then (if i < 403 then (if i < 402 then (i + 737) else (i + 695)) else (if i < 404 then (i + 700) else (if i < 405 then (i + 834) else (i + 837)))) else (if i < 408 then (if i < 407 then (i + 761) else (i + 535)) else (if i < 409 then (i + 828) else (if i < 410 then (i + 831) else (i + 535))))))))) else (if i < 533 then (if i < 492 then (if i < 446 then (if i < 427 then (if i < 420 then (if i < 417 then (if i < 413 then (i + 789) else (i + 535)) else (if i < 418 then (i + 710) else (i + 535))) else (if i < 422 then (if i < 421 then (i + 667) else (i + 670)) else (if i < 423 then (i + 767) else (if i < 426 then (i + 535) else (i + 727))))) else (if i < 433 then (if i < 430 then (if i < 428 then (i + 734) else (i + 535)) else (if i < 431 then (i + 655) else (if i < 432 then (i + 658) else (i + 693)))) else (if i < 443 then (if i < 442 then (i + 535) else (i + 717)) else (if i < 444 then (i + 535) else (if i < 445 then (i + 1) else (i + 749)))))) else (if i < 458 then (if i < 453 then (if i < 449 then (if i < 448 then (i + 533) else (i + 774)) else (if i < 450 then (i + 777) else (i + 533))) else (if i < 455 then (if i < 454 then (i + 809) else (i + 770)) else (if i < 456 then (i + 775) else (if i < 457 then (i + 808) else (i + 809))))) else (if i < 486 then (if i < 482 then (if i < 481 then (i + 533) else (i + 534)) else (if i < 483 then (i + 535) else (if i < 484 then (i + 536) else (i + 537)))) else (if i < 488 then (if i < 487 then (i + 538) else (i + 539)) else (if i < 489 then (i + 540) else (if i < 490 then (i + 541) else (i + 542))))))) else (if i < 513 then (if i < 501 then (if i < 496 then (if i < 494 then (if i < 493 then (i + 543) else (i + 544)) else (if i < 495 then (i + 545) else (i + 546))) else (if i < 498 then (if i < 497 then (i + 547) else (i + 548)) else (if i < 499 then (i + 549) else (if i < 500 then (i + 550) else (i + 551))))) else (if i < 508 then (if i < 503 then (if i < 502 then (i + 552) else (i + 553)) else (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556)))) else (if i < 510 then (if i < 509 then (i + 557) else (i + 558)) else (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561)))))) else (if i < 523 then (if i < 518 then (if i < 515 then (if i < 514 then (i + 562) else (i + 563)) else (if i < 517 then (i + 564) else (i + 565))) else (if i < 520 then (if i < 519 then (i + 566) else (i + 567)) else (if i < 521 then (i + 568) else (if i < 522 then (i + 569) else (i + 570))))) else (if i < 528 then (if i < 525 then (if i < 524 then (i + 571) else (i + 572)) else (if i < 526 then (i + 573) else (if i < 527 then (i + 574) else (i + 575)))) else (if i < 530 then (if i < 529 then (i + 576) else (i + 577)) else (if i < 531 then (i + 578) else (if i < 532 then (i + 579) else (i + 580)))))))) else (if i < 574 then (if i < 554 then (if i < 542 then (if i < 537 then (if i < 535 then (if i < 534 then (i + 581) else (i + 582)) else (if i < 536 then (i + 583) else (i + 584))) else (if i < 539 then (if i < 538 then (i + 585) else (i + 586)) else (if i < 540 then (i + 587) else (if i < 541 then (i + 588) else (i + 589))))) else (if i < 549 then (if i < 544 then (if i < 543 then (i + 590) else (i + 591)) else (if i < 546 then (i + 592) else (if i < 548 then (i + 593) else (i + 594)))) else (if i < 551 then (if i < 550 then (i + 595) else (i + 596)) else (if i < 552 then (i + 597) else (if i < 553 then (i + 598) else (i + 599)))))) else (if i < 563 then (if i < 558 then (if i < 556 then (if i < 555 then (i + 600) else (i + 601)) else (if i < 557 then (i + 602) else (i + 603))) else (if i < 560 then (if i < 559 then (i + 604) else (i + 605)) else (if i < 561 then (i + 606) else (if i < 562 then (i + 607) else (i + 608))))) else (if i < 568 then (if i < 565 then (if i < 564 then (i + 609) else (i + 610)) else (if i < 566 then (i + 611) else (if i < 567 then (i + 612) else (i + 613)))) else (if i < 570 then (if i < 569 then (i + 614) else (i + 615)) else (if i < 571 then (i + 616) else (if i < 572 then (i + 617) else (i + 618))))))) else (if i < 595 then (if i < 584 then (if i < 579 then (if i < 577 then (if i < 575 then (i + 619) else (i + 620)) else (if i < 578 then (i + 621) else (i + 622))) else (if i < 581 then (if i < 580 then (i + 623) else (i + 624)) else (if i < 582 then (i + 625) else (if i < 583 then (i + 626) else (i + 627))))) else (if i < 590 then (if i < 586 then (if i < 585 then (i + 628) else (i + 629)) else (if i < 588 then (i + 630) else (if i < 589 then (i + 631) else (i + 632)))) else (if i < 592 then (if i < 591 then (i + 633) else (i + 634)) else (if i < 593 then (i + 635) else (if i < 594 then (i + 636) else (i + 637)))))) else (if i < 605 then (if i < 600 then (if i < 597 then (if i < 596 then (i + 638) else (i + 639)) else (if i < 598 then (i + 640) else (if i < 599 then (i + 641) else (i + 642)))) else (if i < 602 then (if i < 601 then (i + 643) else (i + 644)) else (if i < 603 then (i + 645) else (if i < 604 then (i + 646) else (i + 647))))) else (if i < 610 then (if i < 607 then (if i < 606 then (i + 648) else (i + 649)) else (if i < 608 then (i + 650) else (if i < 609 then (i + 651) else (i + 652)))) else (if i < 612 then (if i < 611 then (i + 653) else (i + 654)) else (if i < 613 then (i + 655) else (if i < 614 then (i + 656) else (i + 1))))))))))

def steps : List Step := [⟨⟨203,404,[295]⟩,1238⟩,
⟨⟨203,598,[404]⟩,1239⟩,
⟨⟨204,409,[34]⟩,1240⟩,
⟨⟨204,599,[409]⟩,1241⟩,
⟨⟨205,405,[85]⟩,1242⟩,
⟨⟨205,600,[405]⟩,1243⟩,
⟨⟨206,304,[42]⟩,1244⟩,
⟨⟨206,601,[304]⟩,1245⟩,
⟨⟨207,388,[39]⟩,1246⟩,
⟨⟨207,602,[388]⟩,1247⟩,
⟨⟨208,305,[394]⟩,1248⟩,
⟨⟨208,603,[305]⟩,1249⟩,
⟨⟨209,310,[76]⟩,1250⟩,
⟨⟨209,604,[310]⟩,1251⟩,
⟨⟨210,395,[311]⟩,1252⟩,
⟨⟨210,605,[395]⟩,1253⟩,
⟨⟨211,389,[79]⟩,1254⟩,
⟨⟨211,606,[389]⟩,1255⟩,
⟨⟨212,236,[1]⟩,1256⟩,
⟨⟨212,607,[236]⟩,1257⟩,
⟨⟨213,224,[452]⟩,1258⟩,
⟨⟨213,608,[224]⟩,1259⟩,
⟨⟨214,225,[108]⟩,1260⟩,
⟨⟨214,609,[225]⟩,1261⟩,
⟨⟨215,453,[7]⟩,1262⟩,
⟨⟨215,610,[453]⟩,1263⟩,
⟨⟨216,456,[237]⟩,1264⟩,
⟨⟨216,611,[456]⟩,1265⟩,
⟨⟨217,457,[106]⟩,1266⟩,
⟨⟨217,612,[457]⟩,1267⟩,
⟨⟨218,274,[284]⟩,1268⟩,
⟨⟨218,613,[274]⟩,1269⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block018

namespace CSL.Construction.FiniteSSA.Verified.Block019
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block018.after

def after (i : Nat) : Nat := (if i < 427 then (if i < 324 then (if i < 275 then (if i < 245 then (if i < 232 then (if i < 225 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (if i < 224 then (i + 827) else (i + 1034)))) else (if i < 227 then (if i < 226 then (i + 1035) else (i + 1066)) else (if i < 230 then (i + 551) else (if i < 231 then (i + 1068) else (i + 1069))))) else (if i < 237 then (if i < 234 then (if i < 233 then (i + 782) else (i + 551)) else (if i < 235 then (i + 786) else (if i < 236 then (i + 551) else (i + 1020)))) else (if i < 242 then (if i < 240 then (i + 551) else (if i < 241 then (i + 776) else (i + 551))) else (if i < 243 then (i + 776) else (if i < 244 then (i + 780) else (i + 976)))))) else (if i < 261 then (if i < 253 then (if i < 247 then (if i < 246 then (i + 549) else (i + 808)) else (if i < 251 then (i + 549) else (if i < 252 then (i + 977) else (i + 800)))) else (if i < 256 then (if i < 254 then (i + 803) else (i + 547)) else (if i < 257 then (i + 827) else (if i < 260 then (i + 547) else (i + 927))))) else (if i < 269 then (if i < 265 then (if i < 264 then (i + 547) else (i + 855)) else (if i < 266 then (i + 856) else (if i < 268 then (i + 547) else (i + 883)))) else (if i < 272 then (if i < 270 then (i + 886) else (if i < 271 then (i + 922) else (i + 547))) else (if i < 273 then (i + 809) else (if i < 274 then (i + 547) else (i + 994))))))) else (if i < 300 then (if i < 286 then (if i < 281 then (if i < 277 then (if i < 276 then (i + 995) else (i + 1004)) else (if i < 279 then (i + 547) else (if i < 280 then (i + 878) else (i + 837)))) else (if i < 283 then (if i < 282 then (i + 842) else (i + 1004)) else (if i < 284 then (i + 1005) else (if i < 285 then (i + 547) else (i + 989))))) else (if i < 294 then (if i < 291 then (if i < 287 then (i + 809) else (i + 547)) else (if i < 292 then (i + 943) else (if i < 293 then (i + 907) else (i + 547)))) else (if i < 297 then (if i < 295 then (i + 938) else (if i < 296 then (i + 547) else (i + 833))) else (if i < 298 then (i + 547) else (if i < 299 then (i + 865) else (i + 866)))))) else (if i < 312 then (if i < 306 then (if i < 303 then (if i < 302 then (i + 547) else (i + 895)) else (if i < 304 then (i + 902) else (if i < 305 then (i + 940) else (i + 943)))) else (if i < 309 then (if i < 308 then (i + 547) else (i + 785)) else (if i < 310 then (i + 792) else (if i < 311 then (i + 940) else (i + 547))))) else (if i < 318 then (if i < 314 then (if i < 313 then (i + 823) else (i + 547)) else (if i < 315 then (i + 855) else (if i < 316 then (i + 856) else (i + 547)))) else (if i < 321 then (if i < 319 then (i + 709) else (if i < 320 then (i + 547) else (i + 716))) else (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721)))))))) else (if i < 369 then (if i < 347 then (if i < 335 then (if i < 329 then (if i < 326 then (if i < 325 then (i + 701) else (i + 706)) else (if i < 327 then (i + 781) else (if i < 328 then (i + 545) else (i + 813)))) else (if i < 331 then (if i < 330 then (i + 814) else (i + 881)) else (if i < 332 then (i + 882) else (if i < 334 then (i + 543) else (i + 875))))) else (if i < 340 then (if i < 337 then (if i < 336 then (i + 880) else (i + 706)) else (if i < 338 then (i + 709) else (if i < 339 then (i + 767) else (i + 774)))) else (if i < 343 then (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 833))) else (if i < 344 then (i + 840) else (if i < 345 then (i + 685) else (i + 541)))))) else (if i < 357 then (if i < 352 then (if i < 349 then (if i < 348 then (i + 800) else (i + 692)) else (if i < 350 then (i + 541) else (if i < 351 then (i + 761) else (i + 764)))) else (if i < 354 then (if i < 353 then (i + 541) else (i + 865)) else (if i < 355 then (i + 705) else (if i < 356 then (i + 707) else (i + 714))))) else (if i < 363 then (if i < 360 then (if i < 359 then (i + 539) else (i + 705)) else (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 815)))) else (if i < 366 then (if i < 364 then (i + 818) else (if i < 365 then (i + 781) else (i + 539))) else (if i < 367 then (i + 706) else (if i < 368 then (i + 709) else (i + 537))))))) else (if i < 397 then (if i < 381 then (if i < 376 then (if i < 372 then (if i < 370 then (i + 780) else (i + 537)) else (if i < 373 then (i + 702) else (if i < 375 then (i + 537) else (i + 693)))) else (if i < 378 then (if i < 377 then (i + 733) else (i + 537)) else (if i < 379 then (i + 801) else (if i < 380 then (i + 806) else (i + 686))))) else (if i < 389 then (if i < 385 then (if i < 384 then (i + 537) else (i + 747)) else (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858)))) else (if i < 392 then (if i < 390 then (i + 865) else (if i < 391 then (i + 813) else (i + 816))) else (if i < 395 then (i + 537) else (if i < 396 then (i + 857) else (i + 537)))))) else (if i < 409 then (if i < 403 then (if i < 400 then (if i < 398 then (i + 776) else (i + 537)) else (if i < 401 then (i + 733) else (if i < 402 then (i + 737) else (i + 695)))) else (if i < 406 then (if i < 404 then (i + 700) else (if i < 405 then (i + 834) else (i + 837))) else (if i < 407 then (i + 761) else (if i < 408 then (i + 535) else (i + 828))))) else (if i < 418 then (if i < 412 then (if i < 410 then (i + 831) else (i + 535)) else (if i < 413 then (i + 789) else (if i < 417 then (i + 535) else (i + 710)))) else (if i < 422 then (if i < 420 then (i + 535) else (if i < 421 then (i + 667) else (i + 670))) else (if i < 423 then (i + 767) else (if i < 426 then (i + 535) else (i + 727))))))))) else (if i < 541 then (if i < 496 then (if i < 450 then (if i < 439 then (if i < 433 then (if i < 430 then (if i < 428 then (i + 734) else (i + 535)) else (if i < 431 then (i + 655) else (if i < 432 then (i + 658) else (i + 693)))) else (if i < 435 then (if i < 434 then (i + 535) else (i + 848)) else (if i < 437 then (i + 535) else (if i < 438 then (i + 841) else (i + 846))))) else (if i < 444 then (if i < 441 then (if i < 440 then (i + 851) else (i + 832)) else (if i < 442 then (i + 835) else (if i < 443 then (i + 717) else (i + 535)))) else (if i < 447 then (if i < 445 then (i + 1) else (if i < 446 then (i + 749) else (i + 848))) else (if i < 448 then (i + 533) else (if i < 449 then (i + 774) else (i + 777)))))) else (if i < 483 then (if i < 457 then (if i < 454 then (if i < 453 then (i + 533) else (i + 809)) else (if i < 455 then (i + 770) else (if i < 456 then (i + 775) else (i + 808)))) else (if i < 459 then (if i < 458 then (i + 809) else (i + 838)) else (if i < 481 then (i + 533) else (if i < 482 then (i + 534) else (i + 535))))) else (if i < 489 then (if i < 486 then (if i < 484 then (i + 536) else (i + 537)) else (if i < 487 then (i + 538) else (if i < 488 then (i + 539) else (i + 540)))) else (if i < 493 then (if i < 490 then (i + 541) else (if i < 492 then (i + 542) else (i + 543))) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546))))))) else (if i < 520 then (if i < 508 then (if i < 501 then (if i < 498 then (if i < 497 then (i + 547) else (i + 548)) else (if i < 499 then (i + 549) else (if i < 500 then (i + 550) else (i + 551)))) else (if i < 503 then (if i < 502 then (i + 552) else (i + 553)) else (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556))))) else (if i < 513 then (if i < 510 then (if i < 509 then (i + 557) else (i + 558)) else (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561)))) else (if i < 517 then (if i < 514 then (i + 562) else (if i < 515 then (i + 563) else (i + 564))) else (if i < 518 then (i + 565) else (if i < 519 then (i + 566) else (i + 567)))))) else (if i < 530 then (if i < 525 then (if i < 522 then (if i < 521 then (i + 568) else (i + 569)) else (if i < 523 then (i + 570) else (if i < 524 then (i + 571) else (i + 572)))) else (if i < 527 then (if i < 526 then (i + 573) else (i + 574)) else (if i < 528 then (i + 575) else (if i < 529 then (i + 576) else (i + 577))))) else (if i < 535 then (if i < 532 then (if i < 531 then (i + 578) else (i + 579)) else (if i < 533 then (i + 580) else (if i < 534 then (i + 581) else (i + 582)))) else (if i < 538 then (if i < 536 then (i + 583) else (if i < 537 then (i + 584) else (i + 585))) else (if i < 539 then (i + 586) else (if i < 540 then (i + 587) else (i + 588)))))))) else (if i < 588 then (if i < 564 then (if i < 553 then (if i < 548 then (if i < 543 then (if i < 542 then (i + 589) else (i + 590)) else (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593)))) else (if i < 550 then (if i < 549 then (i + 594) else (i + 595)) else (if i < 551 then (i + 596) else (if i < 552 then (i + 597) else (i + 598))))) else (if i < 558 then (if i < 555 then (if i < 554 then (i + 599) else (i + 600)) else (if i < 556 then (i + 601) else (if i < 557 then (i + 602) else (i + 603)))) else (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 562 then (i + 607) else (if i < 563 then (i + 608) else (i + 609)))))) else (if i < 575 then (if i < 569 then (if i < 566 then (if i < 565 then (i + 610) else (i + 611)) else (if i < 567 then (i + 612) else (if i < 568 then (i + 613) else (i + 614)))) else (if i < 571 then (if i < 570 then (i + 615) else (i + 616)) else (if i < 572 then (i + 617) else (if i < 574 then (i + 618) else (i + 619))))) else (if i < 581 then (if i < 578 then (if i < 577 then (i + 620) else (i + 621)) else (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624)))) else (if i < 584 then (if i < 582 then (i + 625) else (if i < 583 then (i + 626) else (i + 627))) else (if i < 585 then (i + 628) else (if i < 586 then (i + 629) else (i + 630))))))) else (if i < 609 then (if i < 598 then (if i < 593 then (if i < 590 then (if i < 589 then (i + 631) else (i + 632)) else (if i < 591 then (i + 633) else (if i < 592 then (i + 634) else (i + 635)))) else (if i < 595 then (if i < 594 then (i + 636) else (i + 637)) else (if i < 596 then (i + 638) else (if i < 597 then (i + 639) else (i + 640))))) else (if i < 603 then (if i < 600 then (if i < 599 then (i + 641) else (i + 642)) else (if i < 601 then (i + 643) else (if i < 602 then (i + 644) else (i + 645)))) else (if i < 606 then (if i < 604 then (i + 646) else (if i < 605 then (i + 647) else (i + 648))) else (if i < 607 then (i + 649) else (if i < 608 then (i + 650) else (i + 651)))))) else (if i < 620 then (if i < 614 then (if i < 611 then (if i < 610 then (i + 652) else (i + 653)) else (if i < 612 then (i + 654) else (if i < 613 then (i + 655) else (i + 656)))) else (if i < 617 then (if i < 615 then (i + 657) else (if i < 616 then (i + 658) else (i + 659))) else (if i < 618 then (i + 660) else (if i < 619 then (i + 661) else (i + 662))))) else (if i < 625 then (if i < 622 then (if i < 621 then (i + 663) else (i + 664)) else (if i < 623 then (i + 665) else (if i < 624 then (i + 666) else (i + 667)))) else (if i < 628 then (if i < 626 then (i + 668) else (if i < 627 then (i + 669) else (i + 670))) else (if i < 629 then (i + 671) else (if i < 630 then (i + 672) else (i + 1))))))))))

def steps : List Step := [⟨⟨219,275,[99]⟩,1270⟩,
⟨⟨219,614,[275]⟩,1271⟩,
⟨⟨220,440,[24]⟩,1272⟩,
⟨⟨220,615,[440]⟩,1273⟩,
⟨⟨221,285,[436]⟩,1274⟩,
⟨⟨221,616,[285]⟩,1275⟩,
⟨⟨222,441,[29]⟩,1276⟩,
⟨⟨222,617,[441]⟩,1277⟩,
⟨⟨223,437,[101]⟩,1278⟩,
⟨⟨223,618,[437]⟩,1279⟩,
⟨⟨224,276,[28]⟩,1280⟩,
⟨⟨224,619,[276]⟩,1281⟩,
⟨⟨225,434,[277]⟩,1282⟩,
⟨⟨225,620,[434]⟩,1283⟩,
⟨⟨226,438,[25]⟩,1284⟩,
⟨⟨226,621,[438]⟩,1285⟩,
⟨⟨227,282,[435]⟩,1286⟩,
⟨⟨227,622,[282]⟩,1287⟩,
⟨⟨228,283,[100]⟩,1288⟩,
⟨⟨228,623,[283]⟩,1289⟩,
⟨⟨229,439,[98]⟩,1290⟩,
⟨⟨229,624,[439]⟩,1291⟩,
⟨⟨230,226,[4]⟩,1292⟩,
⟨⟨230,625,[226]⟩,1293⟩,
⟨⟨231,446,[2]⟩,1294⟩,
⟨⟨231,626,[446]⟩,1295⟩,
⟨⟨232,458,[227]⟩,1296⟩,
⟨⟨232,627,[458]⟩,1297⟩,
⟨⟨233,230,[103]⟩,1298⟩,
⟨⟨233,628,[230]⟩,1299⟩,
⟨⟨234,231,[459]⟩,1300⟩,
⟨⟨234,629,[231]⟩,1301⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block019

namespace CSL.Construction.FiniteSSA.Verified.Block020
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block019.after

def after (i : Nat) : Nat := (if i < 429 then (if i < 324 then (if i < 271 then (if i < 245 then (if i < 233 then (if i < 225 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (if i < 224 then (i + 827) else (i + 1034)))) else (if i < 230 then (if i < 226 then (i + 1035) else (if i < 227 then (i + 1066) else (i + 551))) else (if i < 231 then (i + 1068) else (if i < 232 then (i + 1069) else (i + 782))))) else (if i < 239 then (if i < 236 then (if i < 234 then (i + 551) else (if i < 235 then (i + 786) else (i + 551))) else (if i < 237 then (i + 1020) else (if i < 238 then (i + 551) else (i + 1090)))) else (if i < 242 then (if i < 240 then (i + 1093) else (if i < 241 then (i + 776) else (i + 551))) else (if i < 243 then (i + 776) else (if i < 244 then (i + 780) else (i + 976)))))) else (if i < 259 then (if i < 253 then (if i < 247 then (if i < 246 then (i + 549) else (i + 808)) else (if i < 251 then (i + 549) else (if i < 252 then (i + 977) else (i + 800)))) else (if i < 256 then (if i < 254 then (i + 803) else (if i < 255 then (i + 547) else (i + 1053))) else (if i < 257 then (i + 827) else (if i < 258 then (i + 547) else (i + 1058))))) else (if i < 265 then (if i < 262 then (if i < 260 then (i + 547) else (if i < 261 then (i + 927) else (i + 547))) else (if i < 263 then (i + 1060) else (if i < 264 then (i + 1061) else (i + 855)))) else (if i < 268 then (if i < 266 then (i + 856) else (if i < 267 then (i + 1038) else (i + 1043))) else (if i < 269 then (i + 883) else (if i < 270 then (i + 886) else (i + 922))))))) else (if i < 298 then (if i < 283 then (if i < 276 then (if i < 273 then (if i < 272 then (i + 547) else (i + 809)) else (if i < 274 then (i + 547) else (if i < 275 then (i + 994) else (i + 995)))) else (if i < 280 then (if i < 277 then (i + 1004) else (if i < 279 then (i + 547) else (i + 878))) else (if i < 281 then (i + 837) else (if i < 282 then (i + 842) else (i + 1004))))) else (if i < 292 then (if i < 286 then (if i < 284 then (i + 1005) else (if i < 285 then (i + 547) else (i + 989))) else (if i < 287 then (i + 809) else (if i < 291 then (i + 547) else (i + 943)))) else (if i < 295 then (if i < 293 then (i + 907) else (if i < 294 then (i + 547) else (i + 938))) else (if i < 296 then (i + 547) else (if i < 297 then (i + 833) else (i + 547)))))) else (if i < 311 then (if i < 304 then (if i < 300 then (if i < 299 then (i + 865) else (i + 866)) else (if i < 302 then (i + 547) else (if i < 303 then (i + 895) else (i + 902)))) else (if i < 308 then (if i < 305 then (i + 940) else (if i < 306 then (i + 943) else (i + 547))) else (if i < 309 then (i + 785) else (if i < 310 then (i + 792) else (i + 940))))) else (if i < 318 then (if i < 314 then (if i < 312 then (i + 547) else (if i < 313 then (i + 823) else (i + 547))) else (if i < 315 then (i + 855) else (if i < 316 then (i + 856) else (i + 547)))) else (if i < 321 then (if i < 319 then (i + 709) else (if i < 320 then (i + 547) else (i + 716))) else (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721)))))))) else (if i < 375 then (if i < 349 then (if i < 336 then (if i < 329 then (if i < 326 then (if i < 325 then (i + 701) else (i + 706)) else (if i < 327 then (i + 781) else (if i < 328 then (i + 545) else (i + 813)))) else (if i < 332 then (if i < 330 then (i + 814) else (if i < 331 then (i + 881) else (i + 882))) else (if i < 334 then (i + 543) else (if i < 335 then (i + 875) else (i + 880))))) else (if i < 342 then (if i < 339 then (if i < 337 then (i + 706) else (if i < 338 then (i + 709) else (i + 767))) else (if i < 340 then (i + 774) else (if i < 341 then (i + 541) else (i + 693)))) else (if i < 345 then (if i < 343 then (i + 833) else (if i < 344 then (i + 840) else (i + 685))) else (if i < 347 then (i + 541) else (if i < 348 then (i + 800) else (i + 692)))))) else (if i < 361 then (if i < 354 then (if i < 351 then (if i < 350 then (i + 541) else (i + 761)) else (if i < 352 then (i + 764) else (if i < 353 then (i + 541) else (i + 865)))) else (if i < 357 then (if i < 355 then (i + 705) else (if i < 356 then (i + 707) else (i + 714))) else (if i < 359 then (i + 539) else (if i < 360 then (i + 705) else (i + 539))))) else (if i < 367 then (if i < 364 then (if i < 362 then (i + 717) else (if i < 363 then (i + 815) else (i + 818))) else (if i < 365 then (i + 781) else (if i < 366 then (i + 539) else (i + 706)))) else (if i < 370 then (if i < 368 then (i + 709) else (if i < 369 then (i + 537) else (i + 780))) else (if i < 372 then (i + 537) else (if i < 373 then (i + 702) else (i + 537))))))) else (if i < 404 then (if i < 389 then (if i < 380 then (if i < 377 then (if i < 376 then (i + 693) else (i + 733)) else (if i < 378 then (i + 537) else (if i < 379 then (i + 801) else (i + 806)))) else (if i < 385 then (if i < 381 then (i + 686) else (if i < 384 then (i + 537) else (i + 747))) else (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858))))) else (if i < 397 then (if i < 392 then (if i < 390 then (i + 865) else (if i < 391 then (i + 813) else (i + 816))) else (if i < 395 then (i + 537) else (if i < 396 then (i + 857) else (i + 537)))) else (if i < 401 then (if i < 398 then (i + 776) else (if i < 400 then (i + 537) else (i + 733))) else (if i < 402 then (i + 737) else (if i < 403 then (i + 695) else (i + 700)))))) else (if i < 417 then (if i < 409 then (if i < 406 then (if i < 405 then (i + 834) else (i + 837)) else (if i < 407 then (i + 761) else (if i < 408 then (i + 535) else (i + 828)))) else (if i < 413 then (if i < 410 then (i + 831) else (if i < 412 then (i + 535) else (i + 789))) else (if i < 414 then (i + 535) else (if i < 415 then (i + 904) else (i + 535))))) else (if i < 423 then (if i < 420 then (if i < 418 then (i + 710) else (if i < 419 then (i + 888) else (i + 895))) else (if i < 421 then (i + 667) else (if i < 422 then (i + 670) else (i + 767)))) else (if i < 426 then (if i < 424 then (i + 535) else (if i < 425 then (i + 896) else (i + 901))) else (if i < 427 then (i + 727) else (if i < 428 then (i + 734) else (i + 535))))))))) else (if i < 551 then (if i < 500 then (if i < 454 then (if i < 441 then (if i < 434 then (if i < 431 then (if i < 430 then (i + 883) else (i + 655)) else (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535)))) else (if i < 438 then (if i < 435 then (i + 848) else (if i < 437 then (i + 535) else (i + 841))) else (if i < 439 then (i + 846) else (if i < 440 then (i + 851) else (i + 832))))) else (if i < 447 then (if i < 444 then (if i < 442 then (i + 835) else (if i < 443 then (i + 717) else (i + 535))) else (if i < 445 then (i + 1) else (if i < 446 then (i + 749) else (i + 848)))) else (if i < 450 then (if i < 448 then (i + 855) else (if i < 449 then (i + 774) else (i + 777))) else (if i < 451 then (i + 880) else (if i < 453 then (i + 533) else (i + 809)))))) else (if i < 487 then (if i < 459 then (if i < 456 then (if i < 455 then (i + 770) else (i + 775)) else (if i < 457 then (i + 808) else (if i < 458 then (i + 809) else (i + 838)))) else (if i < 483 then (if i < 481 then (i + 533) else (if i < 482 then (i + 534) else (i + 535))) else (if i < 484 then (i + 536) else (if i < 486 then (i + 537) else (i + 538))))) else (if i < 494 then (if i < 490 then (if i < 488 then (i + 539) else (if i < 489 then (i + 540) else (i + 541))) else (if i < 492 then (i + 542) else (if i < 493 then (i + 543) else (i + 544)))) else (if i < 497 then (if i < 495 then (i + 545) else (if i < 496 then (i + 546) else (i + 547))) else (if i < 498 then (i + 548) else (if i < 499 then (i + 549) else (i + 550))))))) else (if i < 526 then (if i < 513 then (if i < 507 then (if i < 502 then (if i < 501 then (i + 551) else (i + 552)) else (if i < 503 then (i + 553) else (if i < 505 then (i + 554) else (i + 555)))) else (if i < 510 then (if i < 508 then (i + 556) else (if i < 509 then (i + 557) else (i + 558))) else (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561))))) else (if i < 520 then (if i < 517 then (if i < 514 then (i + 562) else (if i < 515 then (i + 563) else (i + 564))) else (if i < 518 then (i + 565) else (if i < 519 then (i + 566) else (i + 567)))) else (if i < 523 then (if i < 521 then (i + 568) else (if i < 522 then (i + 569) else (i + 570))) else (if i < 524 then (i + 571) else (if i < 525 then (i + 572) else (i + 573)))))) else (if i < 537 then (if i < 531 then (if i < 528 then (if i < 527 then (i + 574) else (i + 575)) else (if i < 529 then (i + 576) else (if i < 530 then (i + 577) else (i + 578)))) else (if i < 534 then (if i < 532 then (i + 579) else (if i < 533 then (i + 580) else (i + 581))) else (if i < 535 then (i + 582) else (if i < 536 then (i + 583) else (i + 584))))) else (if i < 543 then (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590)))) else (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 549 then (i + 594) else (if i < 550 then (i + 595) else (i + 596)))))))) else (if i < 600 then (if i < 575 then (if i < 562 then (if i < 556 then (if i < 553 then (if i < 552 then (i + 597) else (i + 598)) else (if i < 554 then (i + 599) else (if i < 555 then (i + 600) else (i + 601)))) else (if i < 559 then (if i < 557 then (i + 602) else (if i < 558 then (i + 603) else (i + 604))) else (if i < 560 then (i + 605) else (if i < 561 then (i + 606) else (i + 607))))) else (if i < 568 then (if i < 565 then (if i < 563 then (i + 608) else (if i < 564 then (i + 609) else (i + 610))) else (if i < 566 then (i + 611) else (if i < 567 then (i + 612) else (i + 613)))) else (if i < 571 then (if i < 569 then (i + 614) else (if i < 570 then (i + 615) else (i + 616))) else (if i < 572 then (i + 617) else (if i < 574 then (i + 618) else (i + 619)))))) else (if i < 588 then (if i < 581 then (if i < 578 then (if i < 577 then (i + 620) else (i + 621)) else (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624)))) else (if i < 584 then (if i < 582 then (i + 625) else (if i < 583 then (i + 626) else (i + 627))) else (if i < 585 then (i + 628) else (if i < 586 then (i + 629) else (i + 630))))) else (if i < 594 then (if i < 591 then (if i < 589 then (i + 631) else (if i < 590 then (i + 632) else (i + 633))) else (if i < 592 then (i + 634) else (if i < 593 then (i + 635) else (i + 636)))) else (if i < 597 then (if i < 595 then (i + 637) else (if i < 596 then (i + 638) else (i + 639))) else (if i < 598 then (i + 640) else (if i < 599 then (i + 641) else (i + 642))))))) else (if i < 623 then (if i < 611 then (if i < 605 then (if i < 602 then (if i < 601 then (i + 643) else (i + 644)) else (if i < 603 then (i + 645) else (if i < 604 then (i + 646) else (i + 647)))) else (if i < 608 then (if i < 606 then (i + 648) else (if i < 607 then (i + 649) else (i + 650))) else (if i < 609 then (i + 651) else (if i < 610 then (i + 652) else (i + 653))))) else (if i < 617 then (if i < 614 then (if i < 612 then (i + 654) else (if i < 613 then (i + 655) else (i + 656))) else (if i < 615 then (i + 657) else (if i < 616 then (i + 658) else (i + 659)))) else (if i < 620 then (if i < 618 then (i + 660) else (if i < 619 then (i + 661) else (i + 662))) else (if i < 621 then (i + 663) else (if i < 622 then (i + 664) else (i + 665)))))) else (if i < 635 then (if i < 629 then (if i < 626 then (if i < 624 then (i + 666) else (if i < 625 then (i + 667) else (i + 668))) else (if i < 627 then (i + 669) else (if i < 628 then (i + 670) else (i + 671)))) else (if i < 632 then (if i < 630 then (i + 672) else (if i < 631 then (i + 673) else (i + 674))) else (if i < 633 then (i + 675) else (if i < 634 then (i + 676) else (i + 677))))) else (if i < 641 then (if i < 638 then (if i < 636 then (i + 678) else (if i < 637 then (i + 679) else (i + 680))) else (if i < 639 then (i + 681) else (if i < 640 then (i + 682) else (i + 683)))) else (if i < 644 then (if i < 642 then (i + 684) else (if i < 643 then (i + 685) else (i + 686))) else (if i < 645 then (i + 687) else (if i < 646 then (i + 688) else (i + 1))))))))))

def steps : List Step := [⟨⟨235,447,[109]⟩,1302⟩,
⟨⟨235,630,[447]⟩,1303⟩,
⟨⟨236,266,[14]⟩,1304⟩,
⟨⟨236,631,[266]⟩,1305⟩,
⟨⟨237,418,[254]⟩,1306⟩,
⟨⟨237,632,[418]⟩,1307⟩,
⟨⟨238,255,[428]⟩,1308⟩,
⟨⟨238,633,[255]⟩,1309⟩,
⟨⟨239,267,[90]⟩,1310⟩,
⟨⟨239,634,[267]⟩,1311⟩,
⟨⟨240,429,[20]⟩,1312⟩,
⟨⟨240,635,[429]⟩,1313⟩,
⟨⟨241,419,[95]⟩,1314⟩,
⟨⟨241,636,[419]⟩,1315⟩,
⟨⟨242,258,[18]⟩,1316⟩,
⟨⟨242,637,[258]⟩,1317⟩,
⟨⟨243,414,[16]⟩,1318⟩,
⟨⟨243,638,[414]⟩,1319⟩,
⟨⟨244,424,[259]⟩,1320⟩,
⟨⟨244,639,[424]⟩,1321⟩,
⟨⟨245,262,[415]⟩,1322⟩,
⟨⟨245,640,[262]⟩,1323⟩,
⟨⟨246,263,[93]⟩,1324⟩,
⟨⟨246,641,[263]⟩,1325⟩,
⟨⟨247,425,[88]⟩,1326⟩,
⟨⟨247,642,[425]⟩,1327⟩,
⟨⟨248,238,[248]⟩,1328⟩,
⟨⟨248,643,[238]⟩,1329⟩,
⟨⟨249,450,[8]⟩,1330⟩,
⟨⟨249,644,[450]⟩,1331⟩,
⟨⟨250,239,[110]⟩,1332⟩,
⟨⟨250,645,[239]⟩,1333⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block020

namespace CSL.Construction.FiniteSSA.Verified.Block021
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block020.after

def after (i : Nat) : Nat := (if i < 431 then (if i < 323 then (if i < 272 then (if i < 246 then (if i < 234 then (if i < 226 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 826))) else (if i < 224 then (i + 827) else (if i < 225 then (i + 1034) else (i + 1035)))) else (if i < 231 then (if i < 227 then (i + 1066) else (if i < 230 then (i + 551) else (i + 1068))) else (if i < 232 then (i + 1069) else (if i < 233 then (i + 782) else (i + 551))))) else (if i < 240 then (if i < 237 then (if i < 235 then (i + 786) else (if i < 236 then (i + 551) else (i + 1020))) else (if i < 238 then (i + 551) else (if i < 239 then (i + 1090) else (i + 1093)))) else (if i < 243 then (if i < 241 then (i + 776) else (if i < 242 then (i + 551) else (i + 776))) else (if i < 244 then (i + 1122) else (if i < 245 then (i + 976) else (i + 549)))))) else (if i < 259 then (if i < 253 then (if i < 250 then (if i < 247 then (i + 808) else (if i < 249 then (i + 549) else (i + 1085))) else (if i < 251 then (i + 549) else (if i < 252 then (i + 977) else (i + 800)))) else (if i < 256 then (if i < 254 then (i + 803) else (if i < 255 then (i + 547) else (i + 1053))) else (if i < 257 then (i + 827) else (if i < 258 then (i + 547) else (i + 1058))))) else (if i < 265 then (if i < 262 then (if i < 260 then (i + 547) else (if i < 261 then (i + 927) else (i + 547))) else (if i < 263 then (i + 1060) else (if i < 264 then (i + 1061) else (i + 855)))) else (if i < 268 then (if i < 266 then (i + 856) else (if i < 267 then (i + 1038) else (i + 1043))) else (if i < 270 then (if i < 269 then (i + 883) else (i + 886)) else (if i < 271 then (i + 922) else (i + 547))))))) else (if i < 298 then (if i < 285 then (if i < 279 then (if i < 275 then (if i < 273 then (i + 809) else (if i < 274 then (i + 547) else (i + 994))) else (if i < 276 then (i + 995) else (if i < 277 then (i + 1004) else (i + 547)))) else (if i < 282 then (if i < 280 then (i + 878) else (if i < 281 then (i + 837) else (i + 842))) else (if i < 283 then (i + 1004) else (if i < 284 then (i + 1005) else (i + 547))))) else (if i < 291 then (if i < 288 then (if i < 286 then (i + 989) else (if i < 287 then (i + 809) else (i + 547))) else (if i < 289 then (i + 1052) else (if i < 290 then (i + 1053) else (i + 547)))) else (if i < 294 then (if i < 292 then (i + 943) else (if i < 293 then (i + 907) else (i + 547))) else (if i < 296 then (if i < 295 then (i + 938) else (i + 547)) else (if i < 297 then (i + 833) else (i + 547)))))) else (if i < 310 then (if i < 304 then (if i < 301 then (if i < 299 then (i + 865) else (if i < 300 then (i + 866) else (i + 1046))) else (if i < 302 then (i + 1047) else (if i < 303 then (i + 895) else (i + 902)))) else (if i < 307 then (if i < 305 then (i + 940) else (if i < 306 then (i + 943) else (i + 1048))) else (if i < 308 then (i + 547) else (if i < 309 then (i + 785) else (i + 792))))) else (if i < 316 then (if i < 313 then (if i < 311 then (i + 940) else (if i < 312 then (i + 547) else (i + 823))) else (if i < 314 then (i + 547) else (if i < 315 then (i + 855) else (i + 856)))) else (if i < 319 then (if i < 317 then (i + 1036) else (if i < 318 then (i + 1043) else (i + 709))) else (if i < 321 then (if i < 320 then (i + 547) else (i + 716)) else (if i < 322 then (i + 717) else (i + 547)))))))) else (if i < 378 then (if i < 350 then (if i < 336 then (if i < 329 then (if i < 326 then (if i < 324 then (i + 721) else (if i < 325 then (i + 701) else (i + 706))) else (if i < 327 then (i + 781) else (if i < 328 then (i + 545) else (i + 813)))) else (if i < 332 then (if i < 330 then (i + 814) else (if i < 331 then (i + 881) else (i + 882))) else (if i < 334 then (i + 543) else (if i < 335 then (i + 875) else (i + 880))))) else (if i < 342 then (if i < 339 then (if i < 337 then (i + 706) else (if i < 338 then (i + 709) else (i + 767))) else (if i < 340 then (i + 774) else (if i < 341 then (i + 541) else (i + 693)))) else (if i < 345 then (if i < 343 then (i + 833) else (if i < 344 then (i + 840) else (i + 685))) else (if i < 348 then (if i < 347 then (i + 541) else (i + 800)) else (if i < 349 then (i + 692) else (i + 541)))))) else (if i < 363 then (if i < 356 then (if i < 353 then (if i < 351 then (i + 761) else (if i < 352 then (i + 764) else (i + 541))) else (if i < 354 then (i + 865) else (if i < 355 then (i + 705) else (i + 707)))) else (if i < 360 then (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705))) else (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 815))))) else (if i < 369 then (if i < 366 then (if i < 364 then (i + 818) else (if i < 365 then (i + 781) else (i + 539))) else (if i < 367 then (i + 706) else (if i < 368 then (i + 709) else (i + 537)))) else (if i < 373 then (if i < 370 then (i + 780) else (if i < 372 then (i + 537) else (i + 702))) else (if i < 376 then (if i < 375 then (i + 537) else (i + 693)) else (if i < 377 then (i + 733) else (i + 537))))))) else (if i < 405 then (if i < 392 then (if i < 385 then (if i < 381 then (if i < 379 then (i + 801) else (if i < 380 then (i + 806) else (i + 686))) else (if i < 383 then (i + 537) else (if i < 384 then (i + 975) else (i + 747)))) else (if i < 389 then (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858))) else (if i < 390 then (i + 865) else (if i < 391 then (i + 813) else (i + 816))))) else (if i < 398 then (if i < 395 then (if i < 393 then (i + 964) else (if i < 394 then (i + 969) else (i + 537))) else (if i < 396 then (i + 857) else (if i < 397 then (i + 537) else (i + 776)))) else (if i < 401 then (if i < 399 then (i + 537) else (if i < 400 then (i + 951) else (i + 733))) else (if i < 403 then (if i < 402 then (i + 737) else (i + 695)) else (if i < 404 then (i + 700) else (i + 834)))))) else (if i < 418 then (if i < 411 then (if i < 408 then (if i < 406 then (i + 837) else (if i < 407 then (i + 761) else (i + 535))) else (if i < 409 then (i + 828) else (if i < 410 then (i + 831) else (i + 934)))) else (if i < 414 then (if i < 412 then (i + 535) else (if i < 413 then (i + 789) else (i + 535))) else (if i < 415 then (i + 904) else (if i < 417 then (i + 535) else (i + 710))))) else (if i < 424 then (if i < 421 then (if i < 419 then (i + 888) else (if i < 420 then (i + 895) else (i + 667))) else (if i < 422 then (i + 670) else (if i < 423 then (i + 767) else (i + 535)))) else (if i < 427 then (if i < 425 then (i + 896) else (if i < 426 then (i + 901) else (i + 727))) else (if i < 429 then (if i < 428 then (i + 734) else (i + 535)) else (if i < 430 then (i + 883) else (i + 655))))))))) else (if i < 558 then (if i < 503 then (if i < 458 then (if i < 444 then (if i < 438 then (if i < 434 then (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535))) else (if i < 435 then (i + 848) else (if i < 437 then (i + 535) else (i + 841)))) else (if i < 441 then (if i < 439 then (i + 846) else (if i < 440 then (i + 851) else (i + 832))) else (if i < 442 then (i + 835) else (if i < 443 then (i + 717) else (i + 535))))) else (if i < 450 then (if i < 447 then (if i < 445 then (i + 1) else (if i < 446 then (i + 749) else (i + 848))) else (if i < 448 then (i + 855) else (if i < 449 then (i + 774) else (i + 777)))) else (if i < 454 then (if i < 451 then (i + 880) else (if i < 453 then (i + 533) else (i + 809))) else (if i < 456 then (if i < 455 then (i + 770) else (i + 775)) else (if i < 457 then (i + 808) else (i + 809)))))) else (if i < 489 then (if i < 482 then (if i < 461 then (if i < 459 then (i + 838) else (if i < 460 then (i + 533) else (i + 876))) else (if i < 462 then (i + 877) else (if i < 481 then (i + 533) else (i + 534)))) else (if i < 486 then (if i < 483 then (i + 535) else (if i < 484 then (i + 536) else (i + 537))) else (if i < 487 then (i + 538) else (if i < 488 then (i + 539) else (i + 540))))) else (if i < 496 then (if i < 493 then (if i < 490 then (i + 541) else (if i < 492 then (i + 542) else (i + 543))) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546)))) else (if i < 499 then (if i < 497 then (i + 547) else (if i < 498 then (i + 548) else (i + 549))) else (if i < 501 then (if i < 500 then (i + 550) else (i + 551)) else (if i < 502 then (i + 552) else (i + 553))))))) else (if i < 531 then (if i < 518 then (if i < 511 then (if i < 508 then (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556))) else (if i < 509 then (i + 557) else (if i < 510 then (i + 558) else (i + 559)))) else (if i < 514 then (if i < 512 then (i + 560) else (if i < 513 then (i + 561) else (i + 562))) else (if i < 515 then (i + 563) else (if i < 517 then (i + 564) else (i + 565))))) else (if i < 524 then (if i < 521 then (if i < 519 then (i + 566) else (if i < 520 then (i + 567) else (i + 568))) else (if i < 522 then (i + 569) else (if i < 523 then (i + 570) else (i + 571)))) else (if i < 527 then (if i < 525 then (i + 572) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 529 then (if i < 528 then (i + 575) else (i + 576)) else (if i < 530 then (i + 577) else (i + 578)))))) else (if i < 543 then (if i < 537 then (if i < 534 then (if i < 532 then (i + 579) else (if i < 533 then (i + 580) else (i + 581))) else (if i < 535 then (i + 582) else (if i < 536 then (i + 583) else (i + 584)))) else (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590))))) else (if i < 551 then (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 549 then (i + 594) else (if i < 550 then (i + 595) else (i + 596)))) else (if i < 554 then (if i < 552 then (i + 597) else (if i < 553 then (i + 598) else (i + 599))) else (if i < 556 then (if i < 555 then (i + 600) else (i + 601)) else (if i < 557 then (i + 602) else (i + 603)))))))) else (if i < 611 then (if i < 585 then (if i < 570 then (if i < 564 then (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 562 then (i + 607) else (if i < 563 then (i + 608) else (i + 609)))) else (if i < 567 then (if i < 565 then (i + 610) else (if i < 566 then (i + 611) else (i + 612))) else (if i < 568 then (i + 613) else (if i < 569 then (i + 614) else (i + 615))))) else (if i < 578 then (if i < 574 then (if i < 571 then (i + 616) else (if i < 572 then (i + 617) else (i + 618))) else (if i < 575 then (i + 619) else (if i < 577 then (i + 620) else (i + 621)))) else (if i < 581 then (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624))) else (if i < 583 then (if i < 582 then (i + 625) else (i + 626)) else (if i < 584 then (i + 627) else (i + 628)))))) else (if i < 598 then (if i < 592 then (if i < 589 then (if i < 586 then (i + 629) else (if i < 588 then (i + 630) else (i + 631))) else (if i < 590 then (i + 632) else (if i < 591 then (i + 633) else (i + 634)))) else (if i < 595 then (if i < 593 then (i + 635) else (if i < 594 then (i + 636) else (i + 637))) else (if i < 596 then (i + 638) else (if i < 597 then (i + 639) else (i + 640))))) else (if i < 604 then (if i < 601 then (if i < 599 then (i + 641) else (if i < 600 then (i + 642) else (i + 643))) else (if i < 602 then (i + 644) else (if i < 603 then (i + 645) else (i + 646)))) else (if i < 607 then (if i < 605 then (i + 647) else (if i < 606 then (i + 648) else (i + 649))) else (if i < 609 then (if i < 608 then (i + 650) else (i + 651)) else (if i < 610 then (i + 652) else (i + 653))))))) else (if i < 636 then (if i < 623 then (if i < 617 then (if i < 614 then (if i < 612 then (i + 654) else (if i < 613 then (i + 655) else (i + 656))) else (if i < 615 then (i + 657) else (if i < 616 then (i + 658) else (i + 659)))) else (if i < 620 then (if i < 618 then (i + 660) else (if i < 619 then (i + 661) else (i + 662))) else (if i < 621 then (i + 663) else (if i < 622 then (i + 664) else (i + 665))))) else (if i < 629 then (if i < 626 then (if i < 624 then (i + 666) else (if i < 625 then (i + 667) else (i + 668))) else (if i < 627 then (i + 669) else (if i < 628 then (i + 670) else (i + 671)))) else (if i < 632 then (if i < 630 then (i + 672) else (if i < 631 then (i + 673) else (i + 674))) else (if i < 634 then (if i < 633 then (i + 675) else (i + 676)) else (if i < 635 then (i + 677) else (i + 678)))))) else (if i < 648 then (if i < 642 then (if i < 639 then (if i < 637 then (i + 679) else (if i < 638 then (i + 680) else (i + 681))) else (if i < 640 then (i + 682) else (if i < 641 then (i + 683) else (i + 684)))) else (if i < 645 then (if i < 643 then (i + 685) else (if i < 644 then (i + 686) else (i + 687))) else (if i < 646 then (i + 688) else (if i < 647 then (i + 689) else (i + 690))))) else (if i < 654 then (if i < 651 then (if i < 649 then (i + 691) else (if i < 650 then (i + 692) else (i + 693))) else (if i < 652 then (i + 694) else (if i < 653 then (i + 695) else (i + 696)))) else (if i < 657 then (if i < 655 then (i + 697) else (if i < 656 then (i + 698) else (i + 699))) else (if i < 659 then (if i < 658 then (i + 700) else (i + 701)) else (if i < 660 then (i + 702) else (i + 703))))))))))

def steps : List Step := [⟨⟨251,249,[105]⟩,1334⟩,
⟨⟨251,646,[249]⟩,1335⟩,
⟨⟨252,460,[12]⟩,1336⟩,
⟨⟨252,647,[460]⟩,1337⟩,
⟨⟨253,461,[451]⟩,1338⟩,
⟨⟨253,648,[461]⟩,1339⟩,
⟨⟨254,288,[37]⟩,1340⟩,
⟨⟨254,649,[288]⟩,1341⟩,
⟨⟨255,289,[398]⟩,1342⟩,
⟨⟨255,650,[289]⟩,1343⟩,
⟨⟨256,410,[31]⟩,1344⟩,
⟨⟨256,651,[410]⟩,1345⟩,
⟨⟨257,300,[81]⟩,1346⟩,
⟨⟨257,652,[300]⟩,1347⟩,
⟨⟨258,301,[411]⟩,1348⟩,
⟨⟨258,653,[301]⟩,1349⟩,
⟨⟨259,399,[86]⟩,1350⟩,
⟨⟨259,654,[399]⟩,1351⟩,
⟨⟨260,316,[40]⟩,1352⟩,
⟨⟨260,655,[316]⟩,1353⟩,
⟨⟨261,306,[382]⟩,1354⟩,
⟨⟨261,656,[306]⟩,1355⟩,
⟨⟨262,392,[307]⟩,1356⟩,
⟨⟨262,657,[392]⟩,1357⟩,
⟨⟨263,383,[45]⟩,1358⟩,
⟨⟨263,658,[383]⟩,1359⟩,
⟨⟨264,317,[78]⟩,1360⟩,
⟨⟨264,659,[317]⟩,1361⟩,
⟨⟨265,393,[73]⟩,1362⟩,
⟨⟨265,660,[393]⟩,1363⟩,
⟨⟨266,243,[244]⟩,1364⟩,
⟨⟨266,243,[236]⟩,1365⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block021

namespace CSL.Construction.FiniteSSA.Verified.Block022
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block021.after

def after (i : Nat) : Nat := (if i < 431 then (if i < 323 then (if i < 272 then (if i < 247 then (if i < 234 then (if i < 226 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 1171))) else (if i < 224 then (i + 827) else (if i < 225 then (i + 1034) else (i + 1035)))) else (if i < 231 then (if i < 227 then (i + 1156) else (if i < 230 then (i + 551) else (i + 1068))) else (if i < 232 then (i + 1069) else (if i < 233 then (i + 782) else (i + 551))))) else (if i < 240 then (if i < 237 then (if i < 235 then (i + 786) else (if i < 236 then (i + 551) else (i + 1149))) else (if i < 238 then (i + 551) else (if i < 239 then (i + 1141) else (i + 1093)))) else (if i < 243 then (if i < 241 then (i + 776) else (if i < 242 then (i + 551) else (i + 776))) else (if i < 245 then (if i < 244 then (i + 1124) else (i + 1143)) else (if i < 246 then (i + 549) else (i + 808)))))) else (if i < 259 then (if i < 253 then (if i < 250 then (if i < 248 then (i + 1124) else (if i < 249 then (i + 549) else (i + 1085))) else (if i < 251 then (i + 549) else (if i < 252 then (i + 977) else (i + 800)))) else (if i < 256 then (if i < 254 then (i + 803) else (if i < 255 then (i + 547) else (i + 1053))) else (if i < 257 then (i + 827) else (if i < 258 then (i + 547) else (i + 1058))))) else (if i < 265 then (if i < 262 then (if i < 260 then (i + 547) else (if i < 261 then (i + 927) else (i + 547))) else (if i < 263 then (i + 1060) else (if i < 264 then (i + 1061) else (i + 855)))) else (if i < 268 then (if i < 266 then (i + 856) else (if i < 267 then (i + 1038) else (i + 1043))) else (if i < 270 then (if i < 269 then (i + 883) else (i + 886)) else (if i < 271 then (i + 922) else (i + 547))))))) else (if i < 298 then (if i < 285 then (if i < 279 then (if i < 275 then (if i < 273 then (i + 809) else (if i < 274 then (i + 547) else (i + 994))) else (if i < 276 then (i + 995) else (if i < 277 then (i + 1004) else (i + 547)))) else (if i < 282 then (if i < 280 then (i + 878) else (if i < 281 then (i + 837) else (i + 842))) else (if i < 283 then (i + 1004) else (if i < 284 then (i + 1005) else (i + 547))))) else (if i < 291 then (if i < 288 then (if i < 286 then (i + 989) else (if i < 287 then (i + 809) else (i + 547))) else (if i < 289 then (i + 1052) else (if i < 290 then (i + 1053) else (i + 547)))) else (if i < 294 then (if i < 292 then (i + 943) else (if i < 293 then (i + 907) else (i + 547))) else (if i < 296 then (if i < 295 then (i + 938) else (i + 547)) else (if i < 297 then (i + 833) else (i + 547)))))) else (if i < 310 then (if i < 304 then (if i < 301 then (if i < 299 then (i + 865) else (if i < 300 then (i + 866) else (i + 1046))) else (if i < 302 then (i + 1047) else (if i < 303 then (i + 895) else (i + 902)))) else (if i < 307 then (if i < 305 then (i + 940) else (if i < 306 then (i + 943) else (i + 1048))) else (if i < 308 then (i + 547) else (if i < 309 then (i + 785) else (i + 792))))) else (if i < 316 then (if i < 313 then (if i < 311 then (i + 940) else (if i < 312 then (i + 547) else (i + 823))) else (if i < 314 then (i + 547) else (if i < 315 then (i + 855) else (i + 856)))) else (if i < 319 then (if i < 317 then (i + 1036) else (if i < 318 then (i + 1043) else (i + 709))) else (if i < 321 then (if i < 320 then (i + 547) else (i + 716)) else (if i < 322 then (i + 717) else (i + 547)))))))) else (if i < 378 then (if i < 350 then (if i < 336 then (if i < 329 then (if i < 326 then (if i < 324 then (i + 721) else (if i < 325 then (i + 701) else (i + 706))) else (if i < 327 then (i + 781) else (if i < 328 then (i + 545) else (i + 813)))) else (if i < 332 then (if i < 330 then (i + 814) else (if i < 331 then (i + 881) else (i + 882))) else (if i < 334 then (i + 543) else (if i < 335 then (i + 875) else (i + 880))))) else (if i < 342 then (if i < 339 then (if i < 337 then (i + 706) else (if i < 338 then (i + 709) else (i + 767))) else (if i < 340 then (i + 774) else (if i < 341 then (i + 541) else (i + 693)))) else (if i < 345 then (if i < 343 then (i + 833) else (if i < 344 then (i + 840) else (i + 685))) else (if i < 348 then (if i < 347 then (i + 541) else (i + 800)) else (if i < 349 then (i + 692) else (i + 541)))))) else (if i < 363 then (if i < 356 then (if i < 353 then (if i < 351 then (i + 761) else (if i < 352 then (i + 1045) else (i + 541))) else (if i < 354 then (i + 865) else (if i < 355 then (i + 705) else (i + 707)))) else (if i < 360 then (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705))) else (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 815))))) else (if i < 369 then (if i < 366 then (if i < 364 then (i + 818) else (if i < 365 then (i + 781) else (i + 539))) else (if i < 367 then (i + 706) else (if i < 368 then (i + 709) else (i + 537)))) else (if i < 373 then (if i < 370 then (i + 780) else (if i < 372 then (i + 537) else (i + 702))) else (if i < 376 then (if i < 375 then (i + 537) else (i + 693)) else (if i < 377 then (i + 733) else (i + 537))))))) else (if i < 405 then (if i < 392 then (if i < 385 then (if i < 381 then (if i < 379 then (i + 801) else (if i < 380 then (i + 1018) else (i + 686))) else (if i < 383 then (i + 537) else (if i < 384 then (i + 975) else (i + 747)))) else (if i < 389 then (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858))) else (if i < 390 then (i + 865) else (if i < 391 then (i + 813) else (i + 816))))) else (if i < 398 then (if i < 395 then (if i < 393 then (i + 964) else (if i < 394 then (i + 969) else (i + 537))) else (if i < 396 then (i + 857) else (if i < 397 then (i + 537) else (i + 776)))) else (if i < 401 then (if i < 399 then (i + 537) else (if i < 400 then (i + 951) else (i + 733))) else (if i < 403 then (if i < 402 then (i + 737) else (i + 695)) else (if i < 404 then (i + 700) else (i + 834)))))) else (if i < 418 then (if i < 411 then (if i < 408 then (if i < 406 then (i + 837) else (if i < 407 then (i + 761) else (i + 535))) else (if i < 409 then (i + 828) else (if i < 410 then (i + 831) else (i + 934)))) else (if i < 414 then (if i < 412 then (i + 535) else (if i < 413 then (i + 789) else (i + 535))) else (if i < 415 then (i + 904) else (if i < 417 then (i + 535) else (i + 710))))) else (if i < 424 then (if i < 421 then (if i < 419 then (i + 888) else (if i < 420 then (i + 895) else (i + 667))) else (if i < 422 then (i + 670) else (if i < 423 then (i + 767) else (i + 535)))) else (if i < 427 then (if i < 425 then (i + 896) else (if i < 426 then (i + 901) else (i + 727))) else (if i < 429 then (if i < 428 then (i + 734) else (i + 535)) else (if i < 430 then (i + 883) else (i + 655))))))))) else (if i < 558 then (if i < 503 then (if i < 458 then (if i < 444 then (if i < 438 then (if i < 434 then (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535))) else (if i < 435 then (i + 848) else (if i < 437 then (i + 535) else (i + 841)))) else (if i < 441 then (if i < 439 then (i + 846) else (if i < 440 then (i + 851) else (i + 832))) else (if i < 442 then (i + 835) else (if i < 443 then (i + 717) else (i + 535))))) else (if i < 450 then (if i < 447 then (if i < 445 then (i + 1) else (if i < 446 then (i + 749) else (i + 848))) else (if i < 448 then (i + 855) else (if i < 449 then (i + 774) else (i + 777)))) else (if i < 454 then (if i < 451 then (i + 880) else (if i < 453 then (i + 533) else (i + 809))) else (if i < 456 then (if i < 455 then (i + 770) else (i + 775)) else (if i < 457 then (i + 808) else (i + 809)))))) else (if i < 489 then (if i < 482 then (if i < 461 then (if i < 459 then (i + 838) else (if i < 460 then (i + 533) else (i + 876))) else (if i < 462 then (i + 877) else (if i < 481 then (i + 533) else (i + 534)))) else (if i < 486 then (if i < 483 then (i + 535) else (if i < 484 then (i + 536) else (i + 537))) else (if i < 487 then (i + 905) else (if i < 488 then (i + 539) else (i + 540))))) else (if i < 496 then (if i < 493 then (if i < 490 then (i + 541) else (if i < 492 then (i + 542) else (i + 543))) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546)))) else (if i < 499 then (if i < 497 then (i + 547) else (if i < 498 then (i + 548) else (i + 549))) else (if i < 501 then (if i < 500 then (i + 550) else (i + 551)) else (if i < 502 then (i + 552) else (i + 553))))))) else (if i < 531 then (if i < 518 then (if i < 511 then (if i < 508 then (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556))) else (if i < 509 then (i + 557) else (if i < 510 then (i + 558) else (i + 559)))) else (if i < 514 then (if i < 512 then (i + 560) else (if i < 513 then (i + 561) else (i + 562))) else (if i < 515 then (i + 563) else (if i < 517 then (i + 564) else (i + 565))))) else (if i < 524 then (if i < 521 then (if i < 519 then (i + 566) else (if i < 520 then (i + 567) else (i + 568))) else (if i < 522 then (i + 569) else (if i < 523 then (i + 570) else (i + 571)))) else (if i < 527 then (if i < 525 then (i + 572) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 529 then (if i < 528 then (i + 575) else (i + 576)) else (if i < 530 then (i + 577) else (i + 578)))))) else (if i < 543 then (if i < 537 then (if i < 534 then (if i < 532 then (i + 579) else (if i < 533 then (i + 580) else (i + 581))) else (if i < 535 then (i + 582) else (if i < 536 then (i + 583) else (i + 584)))) else (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590))))) else (if i < 551 then (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 549 then (i + 594) else (if i < 550 then (i + 595) else (i + 596)))) else (if i < 554 then (if i < 552 then (i + 597) else (if i < 553 then (i + 598) else (i + 599))) else (if i < 556 then (if i < 555 then (i + 600) else (i + 601)) else (if i < 557 then (i + 602) else (i + 603)))))))) else (if i < 611 then (if i < 585 then (if i < 570 then (if i < 564 then (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 562 then (i + 607) else (if i < 563 then (i + 608) else (i + 609)))) else (if i < 567 then (if i < 565 then (i + 610) else (if i < 566 then (i + 611) else (i + 612))) else (if i < 568 then (i + 613) else (if i < 569 then (i + 614) else (i + 615))))) else (if i < 578 then (if i < 574 then (if i < 571 then (i + 616) else (if i < 572 then (i + 617) else (i + 618))) else (if i < 575 then (i + 619) else (if i < 577 then (i + 620) else (i + 621)))) else (if i < 581 then (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624))) else (if i < 583 then (if i < 582 then (i + 625) else (i + 626)) else (if i < 584 then (i + 627) else (i + 628)))))) else (if i < 598 then (if i < 592 then (if i < 589 then (if i < 586 then (i + 629) else (if i < 588 then (i + 630) else (i + 631))) else (if i < 590 then (i + 632) else (if i < 591 then (i + 633) else (i + 634)))) else (if i < 595 then (if i < 593 then (i + 635) else (if i < 594 then (i + 636) else (i + 637))) else (if i < 596 then (i + 638) else (if i < 597 then (i + 639) else (i + 640))))) else (if i < 604 then (if i < 601 then (if i < 599 then (i + 641) else (if i < 600 then (i + 642) else (i + 643))) else (if i < 602 then (i + 644) else (if i < 603 then (i + 645) else (i + 646)))) else (if i < 607 then (if i < 605 then (i + 647) else (if i < 606 then (i + 648) else (i + 649))) else (if i < 609 then (if i < 608 then (i + 650) else (i + 651)) else (if i < 610 then (i + 652) else (i + 653))))))) else (if i < 636 then (if i < 623 then (if i < 617 then (if i < 614 then (if i < 612 then (i + 654) else (if i < 613 then (i + 655) else (i + 656))) else (if i < 615 then (i + 657) else (if i < 616 then (i + 658) else (i + 659)))) else (if i < 620 then (if i < 618 then (i + 660) else (if i < 619 then (i + 661) else (i + 662))) else (if i < 621 then (i + 663) else (if i < 622 then (i + 664) else (i + 665))))) else (if i < 629 then (if i < 626 then (if i < 624 then (i + 666) else (if i < 625 then (i + 667) else (i + 668))) else (if i < 627 then (i + 669) else (if i < 628 then (i + 670) else (i + 671)))) else (if i < 632 then (if i < 630 then (i + 672) else (if i < 631 then (i + 673) else (i + 674))) else (if i < 634 then (if i < 633 then (i + 675) else (i + 676)) else (if i < 635 then (i + 677) else (i + 678)))))) else (if i < 648 then (if i < 642 then (if i < 639 then (if i < 637 then (i + 679) else (if i < 638 then (i + 680) else (i + 681))) else (if i < 640 then (i + 682) else (if i < 641 then (i + 683) else (i + 684)))) else (if i < 645 then (if i < 643 then (i + 685) else (if i < 644 then (i + 686) else (i + 687))) else (if i < 646 then (i + 688) else (if i < 647 then (i + 689) else (i + 690))))) else (if i < 654 then (if i < 651 then (if i < 649 then (i + 691) else (if i < 650 then (i + 692) else (i + 693))) else (if i < 652 then (i + 694) else (if i < 653 then (i + 695) else (i + 696)))) else (if i < 657 then (if i < 655 then (i + 697) else (if i < 656 then (i + 698) else (i + 699))) else (if i < 659 then (if i < 658 then (i + 700) else (i + 701)) else (if i < 660 then (i + 702) else (i + 703))))))))))

def steps : List Step := [⟨⟨266,243,[226]⟩,1366⟩,
⟨⟨266,243,[238]⟩,1367⟩,
⟨⟨266,247,[244]⟩,1368⟩,
⟨⟨266,247,[236]⟩,1369⟩,
⟨⟨266,247,[226]⟩,1370⟩,
⟨⟨266,247,[238]⟩,1371⟩,
⟨⟨266,244,[236]⟩,1372⟩,
⟨⟨266,244,[226]⟩,1373⟩,
⟨⟨266,236,[238]⟩,1374⟩,
⟨⟨266,226,[238]⟩,1375⟩,
⟨⟨266,238,[243]⟩,1376⟩,
⟨⟨266,238,[247]⟩,1377⟩,
⟨⟨266,238,[236]⟩,1378⟩,
⟨⟨266,238,[226]⟩,1379⟩,
⟨⟨266,226,[243]⟩,1380⟩,
⟨⟨266,226,[247]⟩,1381⟩,
⟨⟨266,226,[244]⟩,1382⟩,
⟨⟨266,236,[243]⟩,1383⟩,
⟨⟨266,236,[247]⟩,1384⟩,
⟨⟨266,236,[244]⟩,1385⟩,
⟨⟨266,244,[243]⟩,1386⟩,
⟨⟨266,244,[247]⟩,1387⟩,
⟨⟨267,486,[351]⟩,1388⟩,
⟨⟨267,486,[369]⟩,1389⟩,
⟨⟨267,486,[379]⟩,1390⟩,
⟨⟨267,486,[353]⟩,1391⟩,
⟨⟨267,222,[351]⟩,1392⟩,
⟨⟨267,222,[379]⟩,1393⟩,
⟨⟨267,351,[369]⟩,1394⟩,
⟨⟨267,351,[379]⟩,1395⟩,
⟨⟨267,351,[353]⟩,1396⟩,
⟨⟨267,379,[353]⟩,1397⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block022

namespace CSL.Construction.FiniteSSA.Verified.Block023
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block022.after

def after (i : Nat) : Nat := (if i < 431 then (if i < 323 then (if i < 272 then (if i < 247 then (if i < 234 then (if i < 226 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 1186))) else (if i < 224 then (i + 1193) else (if i < 225 then (i + 1034) else (i + 1035)))) else (if i < 231 then (if i < 227 then (i + 1156) else (if i < 230 then (i + 551) else (i + 1068))) else (if i < 232 then (i + 1069) else (if i < 233 then (i + 782) else (i + 551))))) else (if i < 240 then (if i < 237 then (if i < 235 then (i + 786) else (if i < 236 then (i + 1177) else (i + 1149))) else (if i < 238 then (i + 551) else (if i < 239 then (i + 1141) else (i + 1093)))) else (if i < 243 then (if i < 241 then (i + 776) else (if i < 242 then (i + 551) else (i + 776))) else (if i < 245 then (if i < 244 then (i + 1124) else (i + 1143)) else (if i < 246 then (i + 549) else (i + 808)))))) else (if i < 259 then (if i < 253 then (if i < 250 then (if i < 248 then (i + 1124) else (if i < 249 then (i + 549) else (i + 1085))) else (if i < 251 then (i + 549) else (if i < 252 then (i + 977) else (i + 800)))) else (if i < 256 then (if i < 254 then (i + 803) else (if i < 255 then (i + 547) else (i + 1053))) else (if i < 257 then (i + 827) else (if i < 258 then (i + 547) else (i + 1168))))) else (if i < 265 then (if i < 262 then (if i < 260 then (i + 547) else (if i < 261 then (i + 1169) else (i + 547))) else (if i < 263 then (i + 1060) else (if i < 264 then (i + 1061) else (i + 855)))) else (if i < 268 then (if i < 266 then (i + 856) else (if i < 267 then (i + 1038) else (i + 1043))) else (if i < 270 then (if i < 269 then (i + 883) else (i + 886)) else (if i < 271 then (i + 922) else (i + 547))))))) else (if i < 298 then (if i < 285 then (if i < 279 then (if i < 275 then (if i < 273 then (i + 809) else (if i < 274 then (i + 547) else (i + 1154))) else (if i < 276 then (i + 995) else (if i < 277 then (i + 1004) else (i + 547)))) else (if i < 282 then (if i < 280 then (i + 878) else (if i < 281 then (i + 1138) else (i + 842))) else (if i < 283 then (i + 1004) else (if i < 284 then (i + 1005) else (i + 547))))) else (if i < 291 then (if i < 288 then (if i < 286 then (i + 989) else (if i < 287 then (i + 809) else (i + 547))) else (if i < 289 then (i + 1052) else (if i < 290 then (i + 1053) else (i + 547)))) else (if i < 294 then (if i < 292 then (i + 943) else (if i < 293 then (i + 907) else (i + 547))) else (if i < 296 then (if i < 295 then (i + 938) else (i + 547)) else (if i < 297 then (i + 833) else (i + 547)))))) else (if i < 310 then (if i < 304 then (if i < 301 then (if i < 299 then (i + 865) else (if i < 300 then (i + 866) else (i + 1046))) else (if i < 302 then (i + 1047) else (if i < 303 then (i + 895) else (i + 902)))) else (if i < 307 then (if i < 305 then (i + 940) else (if i < 306 then (i + 943) else (i + 1048))) else (if i < 308 then (i + 547) else (if i < 309 then (i + 785) else (i + 792))))) else (if i < 316 then (if i < 313 then (if i < 311 then (i + 940) else (if i < 312 then (i + 547) else (i + 823))) else (if i < 314 then (i + 547) else (if i < 315 then (i + 855) else (i + 856)))) else (if i < 319 then (if i < 317 then (i + 1036) else (if i < 318 then (i + 1043) else (i + 709))) else (if i < 321 then (if i < 320 then (i + 547) else (i + 716)) else (if i < 322 then (i + 717) else (i + 547)))))))) else (if i < 378 then (if i < 350 then (if i < 336 then (if i < 329 then (if i < 326 then (if i < 324 then (i + 721) else (if i < 325 then (i + 701) else (i + 706))) else (if i < 327 then (i + 781) else (if i < 328 then (i + 545) else (i + 813)))) else (if i < 332 then (if i < 330 then (i + 814) else (if i < 331 then (i + 881) else (i + 882))) else (if i < 334 then (i + 543) else (if i < 335 then (i + 875) else (i + 880))))) else (if i < 342 then (if i < 339 then (if i < 337 then (i + 706) else (if i < 338 then (i + 709) else (i + 767))) else (if i < 340 then (i + 774) else (if i < 341 then (i + 541) else (i + 693)))) else (if i < 345 then (if i < 343 then (i + 833) else (if i < 344 then (i + 840) else (i + 685))) else (if i < 348 then (if i < 347 then (i + 541) else (i + 800)) else (if i < 349 then (i + 692) else (i + 541)))))) else (if i < 363 then (if i < 356 then (if i < 353 then (if i < 351 then (i + 761) else (if i < 352 then (i + 1045) else (i + 541))) else (if i < 354 then (i + 1047) else (if i < 355 then (i + 705) else (i + 707)))) else (if i < 360 then (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705))) else (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 815))))) else (if i < 369 then (if i < 366 then (if i < 364 then (i + 818) else (if i < 365 then (i + 781) else (i + 539))) else (if i < 367 then (i + 706) else (if i < 368 then (i + 709) else (i + 537)))) else (if i < 373 then (if i < 370 then (i + 1038) else (if i < 372 then (i + 537) else (i + 702))) else (if i < 376 then (if i < 375 then (i + 537) else (i + 693)) else (if i < 377 then (i + 733) else (i + 537))))))) else (if i < 405 then (if i < 392 then (if i < 385 then (if i < 381 then (if i < 379 then (i + 801) else (if i < 380 then (i + 1025) else (i + 686))) else (if i < 383 then (i + 537) else (if i < 384 then (i + 975) else (i + 747)))) else (if i < 389 then (if i < 387 then (i + 537) else (if i < 388 then (i + 712) else (i + 858))) else (if i < 390 then (i + 865) else (if i < 391 then (i + 813) else (i + 816))))) else (if i < 398 then (if i < 395 then (if i < 393 then (i + 964) else (if i < 394 then (i + 969) else (i + 537))) else (if i < 396 then (i + 857) else (if i < 397 then (i + 537) else (i + 776)))) else (if i < 401 then (if i < 399 then (i + 537) else (if i < 400 then (i + 951) else (i + 733))) else (if i < 403 then (if i < 402 then (i + 737) else (i + 695)) else (if i < 404 then (i + 700) else (i + 834)))))) else (if i < 418 then (if i < 411 then (if i < 408 then (if i < 406 then (i + 837) else (if i < 407 then (i + 761) else (i + 535))) else (if i < 409 then (i + 828) else (if i < 410 then (i + 831) else (i + 934)))) else (if i < 414 then (if i < 412 then (i + 535) else (if i < 413 then (i + 789) else (i + 535))) else (if i < 415 then (i + 904) else (if i < 417 then (i + 535) else (i + 710))))) else (if i < 424 then (if i < 421 then (if i < 419 then (i + 888) else (if i < 420 then (i + 895) else (i + 667))) else (if i < 422 then (i + 670) else (if i < 423 then (i + 767) else (i + 535)))) else (if i < 427 then (if i < 425 then (i + 896) else (if i < 426 then (i + 901) else (i + 727))) else (if i < 429 then (if i < 428 then (i + 734) else (i + 535)) else (if i < 430 then (i + 883) else (i + 655))))))))) else (if i < 558 then (if i < 503 then (if i < 458 then (if i < 444 then (if i < 438 then (if i < 434 then (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535))) else (if i < 435 then (i + 848) else (if i < 437 then (i + 535) else (i + 841)))) else (if i < 441 then (if i < 439 then (i + 846) else (if i < 440 then (i + 851) else (i + 832))) else (if i < 442 then (i + 835) else (if i < 443 then (i + 717) else (i + 535))))) else (if i < 450 then (if i < 447 then (if i < 445 then (i + 1) else (if i < 446 then (i + 749) else (i + 848))) else (if i < 448 then (i + 855) else (if i < 449 then (i + 774) else (i + 777)))) else (if i < 454 then (if i < 451 then (i + 880) else (if i < 453 then (i + 533) else (i + 809))) else (if i < 456 then (if i < 455 then (i + 770) else (i + 775)) else (if i < 457 then (i + 808) else (i + 809)))))) else (if i < 489 then (if i < 482 then (if i < 461 then (if i < 459 then (i + 838) else (if i < 460 then (i + 533) else (i + 876))) else (if i < 462 then (i + 877) else (if i < 481 then (i + 533) else (i + 534)))) else (if i < 486 then (if i < 483 then (i + 535) else (if i < 484 then (i + 536) else (i + 537))) else (if i < 487 then (i + 905) else (if i < 488 then (i + 539) else (i + 540))))) else (if i < 496 then (if i < 493 then (if i < 490 then (i + 541) else (if i < 492 then (i + 542) else (i + 543))) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546)))) else (if i < 499 then (if i < 497 then (i + 547) else (if i < 498 then (i + 548) else (i + 549))) else (if i < 501 then (if i < 500 then (i + 550) else (i + 551)) else (if i < 502 then (i + 552) else (i + 553))))))) else (if i < 531 then (if i < 518 then (if i < 511 then (if i < 508 then (if i < 505 then (i + 554) else (if i < 507 then (i + 555) else (i + 556))) else (if i < 509 then (i + 557) else (if i < 510 then (i + 558) else (i + 559)))) else (if i < 514 then (if i < 512 then (i + 560) else (if i < 513 then (i + 561) else (i + 562))) else (if i < 515 then (i + 563) else (if i < 517 then (i + 564) else (i + 565))))) else (if i < 524 then (if i < 521 then (if i < 519 then (i + 566) else (if i < 520 then (i + 567) else (i + 568))) else (if i < 522 then (i + 569) else (if i < 523 then (i + 570) else (i + 571)))) else (if i < 527 then (if i < 525 then (i + 572) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 529 then (if i < 528 then (i + 575) else (i + 576)) else (if i < 530 then (i + 577) else (i + 578)))))) else (if i < 543 then (if i < 537 then (if i < 534 then (if i < 532 then (i + 579) else (if i < 533 then (i + 580) else (i + 581))) else (if i < 535 then (i + 582) else (if i < 536 then (i + 583) else (i + 584)))) else (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590))))) else (if i < 551 then (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 549 then (i + 594) else (if i < 550 then (i + 595) else (i + 596)))) else (if i < 554 then (if i < 552 then (i + 597) else (if i < 553 then (i + 598) else (i + 599))) else (if i < 556 then (if i < 555 then (i + 600) else (i + 601)) else (if i < 557 then (i + 602) else (i + 603)))))))) else (if i < 611 then (if i < 585 then (if i < 570 then (if i < 564 then (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 562 then (i + 607) else (if i < 563 then (i + 608) else (i + 609)))) else (if i < 567 then (if i < 565 then (i + 610) else (if i < 566 then (i + 611) else (i + 612))) else (if i < 568 then (i + 613) else (if i < 569 then (i + 614) else (i + 615))))) else (if i < 578 then (if i < 574 then (if i < 571 then (i + 616) else (if i < 572 then (i + 617) else (i + 618))) else (if i < 575 then (i + 619) else (if i < 577 then (i + 620) else (i + 621)))) else (if i < 581 then (if i < 579 then (i + 622) else (if i < 580 then (i + 623) else (i + 624))) else (if i < 583 then (if i < 582 then (i + 625) else (i + 626)) else (if i < 584 then (i + 627) else (i + 628)))))) else (if i < 598 then (if i < 592 then (if i < 589 then (if i < 586 then (i + 629) else (if i < 588 then (i + 630) else (i + 631))) else (if i < 590 then (i + 632) else (if i < 591 then (i + 633) else (i + 634)))) else (if i < 595 then (if i < 593 then (i + 635) else (if i < 594 then (i + 636) else (i + 637))) else (if i < 596 then (i + 638) else (if i < 597 then (i + 639) else (i + 640))))) else (if i < 604 then (if i < 601 then (if i < 599 then (i + 641) else (if i < 600 then (i + 642) else (i + 643))) else (if i < 602 then (i + 644) else (if i < 603 then (i + 645) else (i + 646)))) else (if i < 607 then (if i < 605 then (i + 647) else (if i < 606 then (i + 648) else (i + 649))) else (if i < 609 then (if i < 608 then (i + 650) else (i + 651)) else (if i < 610 then (i + 652) else (i + 653))))))) else (if i < 636 then (if i < 623 then (if i < 617 then (if i < 614 then (if i < 612 then (i + 654) else (if i < 613 then (i + 655) else (i + 656))) else (if i < 615 then (i + 657) else (if i < 616 then (i + 658) else (i + 659)))) else (if i < 620 then (if i < 618 then (i + 660) else (if i < 619 then (i + 661) else (i + 662))) else (if i < 621 then (i + 663) else (if i < 622 then (i + 664) else (i + 665))))) else (if i < 629 then (if i < 626 then (if i < 624 then (i + 666) else (if i < 625 then (i + 667) else (i + 668))) else (if i < 627 then (i + 669) else (if i < 628 then (i + 670) else (i + 671)))) else (if i < 632 then (if i < 630 then (i + 672) else (if i < 631 then (i + 673) else (i + 674))) else (if i < 634 then (if i < 633 then (i + 675) else (i + 676)) else (if i < 635 then (i + 677) else (i + 678)))))) else (if i < 648 then (if i < 642 then (if i < 639 then (if i < 637 then (i + 679) else (if i < 638 then (i + 680) else (i + 681))) else (if i < 640 then (i + 682) else (if i < 641 then (i + 683) else (i + 684)))) else (if i < 645 then (if i < 643 then (i + 685) else (if i < 644 then (i + 686) else (i + 687))) else (if i < 646 then (i + 688) else (if i < 647 then (i + 689) else (i + 690))))) else (if i < 654 then (if i < 651 then (if i < 649 then (i + 691) else (if i < 650 then (i + 692) else (i + 693))) else (if i < 652 then (i + 694) else (if i < 653 then (i + 695) else (i + 696)))) else (if i < 657 then (if i < 655 then (i + 697) else (if i < 656 then (i + 698) else (i + 699))) else (if i < 659 then (if i < 658 then (i + 700) else (i + 701)) else (if i < 660 then (i + 702) else (i + 703))))))))))

def steps : List Step := [⟨⟨267,353,[486]⟩,1398⟩,
⟨⟨267,353,[222]⟩,1399⟩,
⟨⟨267,353,[351]⟩,1400⟩,
⟨⟨267,379,[486]⟩,1401⟩,
⟨⟨267,379,[222]⟩,1402⟩,
⟨⟨267,379,[351]⟩,1403⟩,
⟨⟨267,379,[369]⟩,1404⟩,
⟨⟨267,369,[486]⟩,1405⟩,
⟨⟨267,369,[222]⟩,1406⟩,
⟨⟨267,369,[351]⟩,1407⟩,
⟨⟨267,222,[486]⟩,1408⟩,
⟨⟨268,235,[280]⟩,1409⟩,
⟨⟨268,235,[260]⟩,1410⟩,
⟨⟨268,235,[274]⟩,1411⟩,
⟨⟨268,235,[258]⟩,1412⟩,
⟨⟨268,223,[280]⟩,1413⟩,
⟨⟨268,223,[260]⟩,1414⟩,
⟨⟨268,223,[274]⟩,1415⟩,
⟨⟨268,223,[258]⟩,1416⟩,
⟨⟨268,280,[274]⟩,1417⟩,
⟨⟨268,280,[258]⟩,1418⟩,
⟨⟨268,260,[274]⟩,1419⟩,
⟨⟨268,260,[258]⟩,1420⟩,
⟨⟨268,274,[258]⟩,1421⟩,
⟨⟨268,258,[235]⟩,1422⟩,
⟨⟨268,258,[223]⟩,1423⟩,
⟨⟨268,258,[280]⟩,1424⟩,
⟨⟨268,258,[260]⟩,1425⟩,
⟨⟨268,258,[274]⟩,1426⟩,
⟨⟨268,274,[235]⟩,1427⟩,
⟨⟨268,274,[223]⟩,1428⟩,
⟨⟨268,260,[235]⟩,1429⟩]

theorem checkedTrace : ValidTrace rows before steps := by decide +kernel

theorem checkedIds : ∀ r : Fin 661, runIds steps before r.val = after r.val := by
  apply runIds_eq_of_sparse steps before after 661
  · decide +kernel
  · decide +kernel

theorem checkedBounds : steps.all (fun e => e.gate.destination < 661 &&
    e.gate.sources.all (fun s => s < 661)) = true := by decide +kernel

theorem checkedSources : steps.all (fun e =>
    CSL.Construction.SSAAdjacentChecks.nodupCheck e.gate.sources) = true := by decide +kernel

theorem checkedNoSelf : steps.all (fun e =>
    !e.gate.sources.contains e.gate.destination) = true := by decide +kernel

theorem checkedNodup : ∀ e ∈ steps, e.gate.sources.Nodup := by
  intro e he
  exact CSL.Construction.SSAAdjacentChecks.nodup_of_check _
    ((List.all_eq_true.mp checkedSources) e he)

theorem sound : ArrayBlockSound rows 661 before after steps :=
  arrayBlockSound_of_certificate rows 661 before after steps checkedTrace
    (operandsBound_of_all 661 steps checkedBounds) checkedIds

end
end CSL.Construction.FiniteSSA.Verified.Block023


