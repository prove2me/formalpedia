-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0256To0511
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_Steps0256To0511
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:52:09.981834+00:00
-- url     : https://prove2.me/theorems/a2dffe0f-980d-4289-9e29-d1aa03604636
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / Steps0256To0511
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps0256To0511` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated from ssa-witness.json.gz. All certificates use the Lean kernel.
--   Eight consecutive 32-step certificates share one module and adjacent snapshots.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps0256To0511

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSASparseIndices
import Definitions.Def_CSL_Circuit_Local_SSAAdjacentChecks
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows

/-! Generated from ssa-witness.json.gz. All certificates use the Lean kernel.
Eight consecutive 32-step certificates share one module and adjacent snapshots. -/

namespace CSL.Construction.FiniteSSA.Verified.Block008
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def before (i : Nat) : Nat := (if i < 328 then (if i < 252 then (if i < 242 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 244 then (i + 1) else (i + 549))) else (if i < 324 then (if i < 254 then (i + 1) else (i + 547)) else (if i < 326 then (i + 1) else (i + 545)))) else (if i < 354 then (if i < 334 then (if i < 330 then (i + 1) else (i + 543)) else (if i < 336 then (i + 1) else (i + 541))) else (if i < 366 then (if i < 356 then (i + 1) else (i + 539)) else (if i < 368 then (i + 1) else (if i < 381 then (i + 537) else (i + 1))))))

def after (i : Nat) : Nat := (if i < 330 then (if i < 252 then (if i < 242 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 244 then (i + 1) else (i + 549))) else (if i < 324 then (if i < 254 then (i + 1) else (i + 547)) else (if i < 326 then (i + 1) else (if i < 328 then (i + 545) else (i + 1))))) else (if i < 366 then (if i < 336 then (if i < 334 then (i + 543) else (i + 1)) else (if i < 354 then (i + 541) else (if i < 356 then (i + 1) else (i + 539)))) else (if i < 400 then (if i < 368 then (i + 1) else (i + 537)) else (if i < 402 then (i + 1) else (if i < 415 then (i + 535) else (i + 1))))))

def steps : List Step := [⟨⟨74,381,[72]⟩,918⟩,
⟨⟨75,382,[73]⟩,919⟩,
⟨⟨75,383,[73]⟩,920⟩,
⟨⟨76,384,[74]⟩,921⟩,
⟨⟨76,385,[74]⟩,922⟩,
⟨⟨77,386,[75]⟩,923⟩,
⟨⟨77,387,[75]⟩,924⟩,
⟨⟨78,388,[76]⟩,925⟩,
⟨⟨78,389,[76]⟩,926⟩,
⟨⟨79,390,[77]⟩,927⟩,
⟨⟨79,391,[77]⟩,928⟩,
⟨⟨80,392,[78]⟩,929⟩,
⟨⟨80,393,[78]⟩,930⟩,
⟨⟨81,394,[79]⟩,931⟩,
⟨⟨81,395,[79]⟩,932⟩,
⟨⟨82,396,[80]⟩,933⟩,
⟨⟨82,397,[80]⟩,934⟩,
⟨⟨83,398,[81]⟩,935⟩,
⟨⟨83,399,[81]⟩,936⟩,
⟨⟨84,402,[82]⟩,937⟩,
⟨⟨84,403,[82]⟩,938⟩,
⟨⟨85,404,[83]⟩,939⟩,
⟨⟨85,405,[83]⟩,940⟩,
⟨⟨86,406,[84]⟩,941⟩,
⟨⟨86,407,[84]⟩,942⟩,
⟨⟨87,408,[85]⟩,943⟩,
⟨⟨87,409,[85]⟩,944⟩,
⟨⟨88,410,[86]⟩,945⟩,
⟨⟨88,411,[86]⟩,946⟩,
⟨⟨89,412,[87]⟩,947⟩,
⟨⟨89,413,[87]⟩,948⟩,
⟨⟨90,414,[88]⟩,949⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block008

namespace CSL.Construction.FiniteSSA.Verified.Block009
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block008.after

def after (i : Nat) : Nat := (if i < 334 then (if i < 254 then (if i < 242 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 244 then (i + 1) else (if i < 252 then (i + 549) else (i + 1)))) else (if i < 326 then (if i < 324 then (i + 547) else (i + 1)) else (if i < 328 then (i + 545) else (if i < 330 then (i + 1) else (i + 543))))) else (if i < 368 then (if i < 354 then (if i < 336 then (i + 1) else (i + 541)) else (if i < 356 then (i + 1) else (if i < 366 then (i + 539) else (i + 1)))) else (if i < 444 then (if i < 400 then (i + 537) else (if i < 402 then (i + 1) else (i + 535))) else (if i < 446 then (i + 1) else (if i < 449 then (i + 533) else (i + 1))))))

def steps : List Step := [⟨⟨90,415,[88]⟩,950⟩,
⟨⟨91,416,[89]⟩,951⟩,
⟨⟨91,417,[89]⟩,952⟩,
⟨⟨92,418,[90]⟩,953⟩,
⟨⟨92,419,[90]⟩,954⟩,
⟨⟨93,420,[91]⟩,955⟩,
⟨⟨93,421,[91]⟩,956⟩,
⟨⟨94,422,[92]⟩,957⟩,
⟨⟨94,423,[92]⟩,958⟩,
⟨⟨95,424,[93]⟩,959⟩,
⟨⟨95,425,[93]⟩,960⟩,
⟨⟨96,426,[94]⟩,961⟩,
⟨⟨96,427,[94]⟩,962⟩,
⟨⟨97,428,[95]⟩,963⟩,
⟨⟨97,429,[95]⟩,964⟩,
⟨⟨98,430,[96]⟩,965⟩,
⟨⟨98,431,[96]⟩,966⟩,
⟨⟨99,432,[97]⟩,967⟩,
⟨⟨99,433,[97]⟩,968⟩,
⟨⟨100,434,[98]⟩,969⟩,
⟨⟨100,435,[98]⟩,970⟩,
⟨⟨101,436,[99]⟩,971⟩,
⟨⟨101,437,[99]⟩,972⟩,
⟨⟨102,438,[100]⟩,973⟩,
⟨⟨102,439,[100]⟩,974⟩,
⟨⟨103,440,[101]⟩,975⟩,
⟨⟨103,441,[101]⟩,976⟩,
⟨⟨104,442,[102]⟩,977⟩,
⟨⟨104,443,[102]⟩,978⟩,
⟨⟨105,446,[103]⟩,979⟩,
⟨⟨105,447,[103]⟩,980⟩,
⟨⟨106,448,[104]⟩,981⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block009

namespace CSL.Construction.FiniteSSA.Verified.Block010
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block009.after

def after (i : Nat) : Nat := (if i < 334 then (if i < 254 then (if i < 242 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 244 then (i + 1) else (if i < 252 then (i + 549) else (i + 1)))) else (if i < 326 then (if i < 324 then (i + 547) else (i + 1)) else (if i < 328 then (i + 545) else (if i < 330 then (i + 1) else (i + 543))))) else (if i < 368 then (if i < 354 then (if i < 336 then (i + 1) else (i + 541)) else (if i < 356 then (i + 1) else (if i < 366 then (i + 539) else (i + 1)))) else (if i < 444 then (if i < 400 then (i + 537) else (if i < 402 then (i + 1) else (i + 535))) else (if i < 446 then (i + 1) else (if i < 481 then (i + 533) else (i + 1))))))

def steps : List Step := [⟨⟨106,449,[104]⟩,982⟩,
⟨⟨107,450,[105]⟩,983⟩,
⟨⟨107,451,[105]⟩,984⟩,
⟨⟨108,452,[106]⟩,985⟩,
⟨⟨108,453,[106]⟩,986⟩,
⟨⟨109,454,[107]⟩,987⟩,
⟨⟨109,455,[107]⟩,988⟩,
⟨⟨110,456,[108]⟩,989⟩,
⟨⟨110,457,[108]⟩,990⟩,
⟨⟨111,458,[109]⟩,991⟩,
⟨⟨111,459,[109]⟩,992⟩,
⟨⟨112,460,[110]⟩,993⟩,
⟨⟨112,461,[110]⟩,994⟩,
⟨⟨49,462,[47]⟩,995⟩,
⟨⟨54,463,[52]⟩,996⟩,
⟨⟨56,464,[54]⟩,997⟩,
⟨⟨2,465,[0]⟩,998⟩,
⟨⟨21,466,[19]⟩,999⟩,
⟨⟨29,467,[27]⟩,1000⟩,
⟨⟨40,468,[38]⟩,1001⟩,
⟨⟨52,469,[50]⟩,1002⟩,
⟨⟨79,470,[77]⟩,1003⟩,
⟨⟨94,471,[92]⟩,1004⟩,
⟨⟨8,472,[6]⟩,1005⟩,
⟨⟨13,473,[11]⟩,1006⟩,
⟨⟨58,474,[56]⟩,1007⟩,
⟨⟨59,475,[57]⟩,1008⟩,
⟨⟨69,476,[67]⟩,1009⟩,
⟨⟨71,477,[69]⟩,1010⟩,
⟨⟨70,478,[68]⟩,1011⟩,
⟨⟨45,479,[43]⟩,1012⟩,
⟨⟨19,480,[17]⟩,1013⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block010

namespace CSL.Construction.FiniteSSA.Verified.Block011
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block010.after

def after (i : Nat) : Nat := (if i < 342 then (if i < 319 then (if i < 241 then (if i < 233 then (if i < 111 then (i + 1) else (if i < 232 then (i + 551) else (i + 782))) else (if i < 235 then (if i < 234 then (i + 551) else (i + 786)) else (if i < 240 then (i + 551) else (i + 776)))) else (if i < 244 then (if i < 242 then (i + 551) else (if i < 243 then (i + 776) else (i + 780))) else (if i < 254 then (if i < 252 then (i + 549) else (i + 1)) else (if i < 318 then (i + 547) else (i + 709))))) else (if i < 326 then (if i < 322 then (if i < 320 then (i + 547) else (if i < 321 then (i + 716) else (i + 717))) else (if i < 324 then (if i < 323 then (i + 547) else (i + 721)) else (if i < 325 then (i + 701) else (i + 706)))) else (if i < 334 then (if i < 328 then (i + 545) else (if i < 330 then (i + 1) else (i + 543))) else (if i < 337 then (if i < 336 then (i + 1) else (i + 706)) else (if i < 341 then (i + 541) else (i + 693)))))) else (if i < 482 then (if i < 366 then (if i < 348 then (if i < 344 then (i + 541) else (if i < 345 then (i + 685) else (i + 541))) else (if i < 354 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 356 then (i + 1) else (i + 539)))) else (if i < 402 then (if i < 368 then (i + 1) else (if i < 400 then (i + 537) else (i + 1))) else (if i < 446 then (if i < 444 then (i + 535) else (i + 1)) else (if i < 481 then (i + 533) else (i + 534))))) else (if i < 490 then (if i < 486 then (if i < 483 then (i + 535) else (if i < 484 then (i + 536) else (i + 537))) else (if i < 488 then (if i < 487 then (i + 538) else (i + 539)) else (if i < 489 then (i + 540) else (i + 541)))) else (if i < 495 then (if i < 493 then (if i < 492 then (i + 542) else (i + 543)) else (if i < 494 then (i + 544) else (i + 545))) else (if i < 497 then (if i < 496 then (i + 546) else (i + 547)) else (if i < 498 then (i + 548) else (i + 1)))))))

def steps : List Step := [⟨⟨113,232,[6]⟩,1014⟩,
⟨⟨113,481,[232]⟩,1015⟩,
⟨⟨114,240,[5]⟩,1016⟩,
⟨⟨114,482,[240]⟩,1017⟩,
⟨⟨7,242,[233]⟩,1018⟩,
⟨⟨7,483,[242]⟩,1019⟩,
⟨⟨115,234,[241]⟩,1020⟩,
⟨⟨115,484,[234]⟩,1021⟩,
⟨⟨8,485,[235]⟩,1022⟩,
⟨⟨11,243,[9]⟩,1023⟩,
⟨⟨11,486,[243]⟩,1024⟩,
⟨⟨48,324,[46]⟩,1025⟩,
⟨⟨48,487,[324]⟩,1026⟩,
⟨⟨116,318,[340]⟩,1027⟩,
⟨⟨116,488,[318]⟩,1028⟩,
⟨⟨117,344,[319]⟩,1029⟩,
⟨⟨117,489,[344]⟩,1030⟩,
⟨⟨56,325,[54]⟩,1031⟩,
⟨⟨56,490,[325]⟩,1032⟩,
⟨⟨58,491,[345]⟩,1033⟩,
⟨⟨118,341,[56]⟩,1034⟩,
⟨⟨118,492,[341]⟩,1035⟩,
⟨⟨119,320,[48]⟩,1036⟩,
⟨⟨119,493,[320]⟩,1037⟩,
⟨⟨120,321,[52]⟩,1038⟩,
⟨⟨120,494,[321]⟩,1039⟩,
⟨⟨121,348,[47]⟩,1040⟩,
⟨⟨121,495,[348]⟩,1041⟩,
⟨⟨122,336,[322]⟩,1042⟩,
⟨⟨122,496,[336]⟩,1043⟩,
⟨⟨123,323,[349]⟩,1044⟩,
⟨⟨123,497,[323]⟩,1045⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block011

namespace CSL.Construction.FiniteSSA.Verified.Block012
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block011.after

def after (i : Nat) : Nat := (if i < 360 then (if i < 321 then (if i < 242 then (if i < 232 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (if i < 224 then (i + 827) else (i + 551)))) else (if i < 235 then (if i < 233 then (i + 782) else (if i < 234 then (i + 551) else (i + 786))) else (if i < 240 then (i + 551) else (if i < 241 then (i + 776) else (i + 551))))) else (if i < 252 then (if i < 244 then (if i < 243 then (i + 776) else (i + 780)) else (if i < 246 then (i + 549) else (if i < 247 then (i + 808) else (i + 549)))) else (if i < 318 then (if i < 253 then (i + 800) else (if i < 254 then (i + 803) else (i + 547))) else (if i < 319 then (i + 709) else (if i < 320 then (i + 547) else (i + 716)))))) else (if i < 338 then (if i < 326 then (if i < 323 then (if i < 322 then (i + 717) else (i + 547)) else (if i < 324 then (i + 721) else (if i < 325 then (i + 701) else (i + 706)))) else (if i < 334 then (if i < 328 then (i + 545) else (if i < 330 then (i + 1) else (i + 543))) else (if i < 336 then (i + 1) else (if i < 337 then (i + 706) else (i + 709))))) else (if i < 349 then (if i < 344 then (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 541))) else (if i < 345 then (i + 685) else (if i < 348 then (i + 541) else (i + 692)))) else (if i < 356 then (if i < 354 then (i + 541) else (if i < 355 then (i + 705) else (i + 707))) else (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705))))))) else (if i < 490 then (if i < 402 then (if i < 373 then (if i < 367 then (if i < 366 then (i + 539) else (i + 706)) else (if i < 368 then (i + 709) else (if i < 372 then (i + 537) else (i + 702)))) else (if i < 380 then (if i < 375 then (i + 537) else (if i < 376 then (i + 693) else (i + 537))) else (if i < 381 then (i + 686) else (if i < 400 then (i + 537) else (i + 1))))) else (if i < 483 then (if i < 446 then (if i < 444 then (i + 535) else (i + 1)) else (if i < 481 then (i + 533) else (if i < 482 then (i + 534) else (i + 535)))) else (if i < 487 then (if i < 484 then (i + 536) else (if i < 486 then (i + 537) else (i + 538))) else (if i < 488 then (i + 539) else (if i < 489 then (i + 540) else (i + 541)))))) else (if i < 502 then (if i < 496 then (if i < 493 then (if i < 492 then (i + 542) else (i + 543)) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546)))) else (if i < 499 then (if i < 497 then (i + 547) else (if i < 498 then (i + 548) else (i + 549))) else (if i < 500 then (i + 550) else (if i < 501 then (i + 551) else (i + 552))))) else (if i < 510 then (if i < 507 then (if i < 503 then (i + 553) else (if i < 505 then (i + 554) else (i + 555))) else (if i < 508 then (i + 556) else (if i < 509 then (i + 557) else (i + 558)))) else (if i < 513 then (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561))) else (if i < 514 then (i + 562) else (if i < 515 then (i + 563) else (i + 1))))))))

def steps : List Step := [⟨⟨124,337,[58]⟩,1046⟩,
⟨⟨124,498,[337]⟩,1047⟩,
⟨⟨125,222,[228]⟩,1048⟩,
⟨⟨125,499,[222]⟩,1049⟩,
⟨⟨126,223,[11]⟩,1050⟩,
⟨⟨126,500,[223]⟩,1051⟩,
⟨⟨2,252,[0]⟩,1052⟩,
⟨⟨2,501,[252]⟩,1053⟩,
⟨⟨127,246,[3]⟩,1054⟩,
⟨⟨127,502,[246]⟩,1055⟩,
⟨⟨5,253,[229]⟩,1056⟩,
⟨⟨5,503,[253]⟩,1057⟩,
⟨⟨13,504,[247]⟩,1058⟩,
⟨⟨64,354,[358]⟩,1059⟩,
⟨⟨64,505,[354]⟩,1060⟩,
⟨⟨71,506,[374]⟩,1061⟩,
⟨⟨74,355,[72]⟩,1062⟩,
⟨⟨74,507,[355]⟩,1063⟩,
⟨⟨128,359,[69]⟩,1064⟩,
⟨⟨128,508,[359]⟩,1065⟩,
⟨⟨129,380,[62]⟩,1066⟩,
⟨⟨129,509,[380]⟩,1067⟩,
⟨⟨130,375,[381]⟩,1068⟩,
⟨⟨130,510,[375]⟩,1069⟩,
⟨⟨131,356,[63]⟩,1070⟩,
⟨⟨131,511,[356]⟩,1071⟩,
⟨⟨63,366,[61]⟩,1072⟩,
⟨⟨63,512,[366]⟩,1073⟩,
⟨⟨132,372,[357]⟩,1074⟩,
⟨⟨132,513,[372]⟩,1075⟩,
⟨⟨65,367,[360]⟩,1076⟩,
⟨⟨65,514,[367]⟩,1077⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block012

namespace CSL.Construction.FiniteSSA.Verified.Block013
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block012.after

def after (i : Nat) : Nat := (if i < 375 then (if i < 322 then (if i < 252 then (if i < 235 then (if i < 224 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (i + 827))) else (if i < 233 then (if i < 232 then (i + 551) else (i + 782)) else (if i < 234 then (i + 551) else (i + 786)))) else (if i < 243 then (if i < 241 then (if i < 240 then (i + 551) else (i + 776)) else (if i < 242 then (i + 551) else (i + 776))) else (if i < 246 then (if i < 244 then (i + 780) else (i + 549)) else (if i < 247 then (i + 808) else (i + 549))))) else (if i < 287 then (if i < 257 then (if i < 254 then (if i < 253 then (i + 800) else (i + 803)) else (if i < 256 then (i + 547) else (i + 827))) else (if i < 273 then (if i < 272 then (i + 547) else (i + 809)) else (if i < 286 then (i + 547) else (i + 809)))) else (if i < 318 then (if i < 309 then (if i < 308 then (i + 547) else (i + 785)) else (if i < 310 then (i + 792) else (i + 547))) else (if i < 320 then (if i < 319 then (i + 709) else (i + 547)) else (if i < 321 then (i + 716) else (i + 717)))))) else (if i < 345 then (if i < 334 then (if i < 326 then (if i < 324 then (if i < 323 then (i + 547) else (i + 721)) else (if i < 325 then (i + 701) else (i + 706))) else (if i < 328 then (if i < 327 then (i + 781) else (i + 545)) else (if i < 330 then (i + 1) else (i + 543)))) else (if i < 339 then (if i < 337 then (if i < 336 then (i + 1) else (i + 706)) else (if i < 338 then (i + 709) else (i + 767))) else (if i < 342 then (if i < 341 then (i + 541) else (i + 693)) else (if i < 344 then (i + 541) else (i + 685))))) else (if i < 360 then (if i < 355 then (if i < 349 then (if i < 348 then (i + 541) else (i + 692)) else (if i < 354 then (i + 541) else (i + 705))) else (if i < 357 then (if i < 356 then (i + 707) else (i + 714)) else (if i < 359 then (i + 539) else (i + 705)))) else (if i < 367 then (if i < 362 then (if i < 361 then (i + 539) else (i + 717)) else (if i < 366 then (i + 539) else (i + 706))) else (if i < 372 then (if i < 368 then (i + 709) else (i + 537)) else (if i < 373 then (i + 702) else (i + 537))))))) else (if i < 496 then (if i < 432 then (if i < 402 then (if i < 381 then (if i < 377 then (if i < 376 then (i + 693) else (i + 733)) else (if i < 380 then (i + 537) else (i + 686))) else (if i < 388 then (if i < 387 then (i + 537) else (i + 712)) else (if i < 400 then (i + 537) else (i + 1)))) else (if i < 421 then (if i < 404 then (if i < 403 then (i + 695) else (i + 700)) else (if i < 420 then (i + 535) else (i + 667))) else (if i < 430 then (if i < 422 then (i + 670) else (i + 535)) else (if i < 431 then (i + 655) else (i + 658))))) else (if i < 487 then (if i < 482 then (if i < 446 then (if i < 444 then (i + 535) else (i + 1)) else (if i < 481 then (i + 533) else (i + 534))) else (if i < 484 then (if i < 483 then (i + 535) else (i + 536)) else (if i < 486 then (i + 537) else (i + 538)))) else (if i < 492 then (if i < 489 then (if i < 488 then (i + 539) else (i + 540)) else (if i < 490 then (i + 541) else (i + 542))) else (if i < 494 then (if i < 493 then (i + 543) else (i + 544)) else (if i < 495 then (i + 545) else (i + 546)))))) else (if i < 514 then (if i < 505 then (if i < 500 then (if i < 498 then (if i < 497 then (i + 547) else (i + 548)) else (if i < 499 then (i + 549) else (i + 550))) else (if i < 502 then (if i < 501 then (i + 551) else (i + 552)) else (if i < 503 then (i + 553) else (i + 554)))) else (if i < 510 then (if i < 508 then (if i < 507 then (i + 555) else (i + 556)) else (if i < 509 then (i + 557) else (i + 558))) else (if i < 512 then (if i < 511 then (i + 559) else (i + 560)) else (if i < 513 then (i + 561) else (i + 562))))) else (if i < 523 then (if i < 519 then (if i < 517 then (if i < 515 then (i + 563) else (i + 564)) else (if i < 518 then (i + 565) else (i + 566))) else (if i < 521 then (if i < 520 then (i + 567) else (i + 568)) else (if i < 522 then (i + 569) else (i + 570)))) else (if i < 527 then (if i < 525 then (if i < 524 then (i + 571) else (i + 572)) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 529 then (if i < 528 then (i + 575) else (i + 576)) else (if i < 530 then (i + 577) else (if i < 531 then (i + 578) else (i + 1)))))))))

def steps : List Step := [⟨⟨133,361,[68]⟩,1078⟩,
⟨⟨133,515,[361]⟩,1079⟩,
⟨⟨70,516,[373]⟩,1080⟩,
⟨⟨134,272,[15]⟩,1081⟩,
⟨⟨134,517,[272]⟩,1082⟩,
⟨⟨135,256,[91]⟩,1083⟩,
⟨⟨135,518,[256]⟩,1084⟩,
⟨⟨136,430,[257]⟩,1085⟩,
⟨⟨136,519,[430]⟩,1086⟩,
⟨⟨137,420,[23]⟩,1087⟩,
⟨⟨137,520,[420]⟩,1088⟩,
⟨⟨138,431,[273]⟩,1089⟩,
⟨⟨138,521,[431]⟩,1090⟩,
⟨⟨139,421,[96]⟩,1091⟩,
⟨⟨139,522,[421]⟩,1092⟩,
⟨⟨140,308,[30]⟩,1093⟩,
⟨⟨140,523,[308]⟩,1094⟩,
⟨⟨141,286,[386]⟩,1095⟩,
⟨⟨141,524,[286]⟩,1096⟩,
⟨⟨142,402,[287]⟩,1097⟩,
⟨⟨142,525,[402]⟩,1098⟩,
⟨⟨143,387,[41]⟩,1099⟩,
⟨⟨143,526,[387]⟩,1100⟩,
⟨⟨144,309,[82]⟩,1101⟩,
⟨⟨144,527,[309]⟩,1102⟩,
⟨⟨145,403,[75]⟩,1103⟩,
⟨⟨145,528,[403]⟩,1104⟩,
⟨⟨146,338,[49]⟩,1105⟩,
⟨⟨146,529,[338]⟩,1106⟩,
⟨⟨147,326,[59]⟩,1107⟩,
⟨⟨147,530,[326]⟩,1108⟩,
⟨⟨148,376,[327]⟩,1109⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block013

namespace CSL.Construction.FiniteSSA.Verified.Block014
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block013.after

def after (i : Nat) : Nat := (if i < 380 then (if i < 321 then (if i < 257 then (if i < 241 then (if i < 232 then (if i < 222 then (if i < 111 then (i + 1) else (i + 551)) else (if i < 223 then (i + 826) else (if i < 224 then (i + 827) else (i + 551)))) else (if i < 234 then (if i < 233 then (i + 782) else (i + 551)) else (if i < 235 then (i + 786) else (if i < 240 then (i + 551) else (i + 776))))) else (if i < 247 then (if i < 243 then (if i < 242 then (i + 551) else (i + 776)) else (if i < 244 then (i + 780) else (if i < 246 then (i + 549) else (i + 808)))) else (if i < 253 then (if i < 252 then (i + 549) else (i + 800)) else (if i < 254 then (i + 803) else (if i < 256 then (i + 547) else (i + 827)))))) else (if i < 287 then (if i < 273 then (if i < 265 then (if i < 264 then (i + 547) else (i + 855)) else (if i < 266 then (i + 856) else (if i < 272 then (i + 547) else (i + 809)))) else (if i < 281 then (if i < 280 then (i + 547) else (i + 837)) else (if i < 282 then (i + 842) else (if i < 286 then (i + 547) else (i + 809))))) else (if i < 310 then (if i < 297 then (if i < 296 then (i + 547) else (i + 833)) else (if i < 308 then (i + 547) else (if i < 309 then (i + 785) else (i + 792)))) else (if i < 318 then (if i < 312 then (i + 547) else (if i < 313 then (i + 823) else (i + 547))) else (if i < 319 then (i + 709) else (if i < 320 then (i + 547) else (i + 716))))))) else (if i < 348 then (if i < 334 then (if i < 326 then (if i < 323 then (if i < 322 then (i + 717) else (i + 547)) else (if i < 324 then (i + 721) else (if i < 325 then (i + 701) else (i + 706)))) else (if i < 328 then (if i < 327 then (i + 781) else (i + 545)) else (if i < 329 then (i + 813) else (if i < 330 then (i + 1) else (i + 543))))) else (if i < 340 then (if i < 337 then (if i < 336 then (i + 1) else (i + 706)) else (if i < 338 then (i + 709) else (if i < 339 then (i + 767) else (i + 774)))) else (if i < 342 then (if i < 341 then (i + 541) else (i + 693)) else (if i < 344 then (i + 541) else (if i < 345 then (i + 685) else (i + 541)))))) else (if i < 360 then (if i < 354 then (if i < 350 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 351 then (i + 761) else (if i < 352 then (i + 764) else (i + 541)))) else (if i < 356 then (if i < 355 then (i + 705) else (i + 707)) else (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705))))) else (if i < 368 then (if i < 362 then (if i < 361 then (i + 539) else (i + 717)) else (if i < 366 then (i + 539) else (if i < 367 then (i + 706) else (i + 709)))) else (if i < 375 then (if i < 372 then (i + 537) else (if i < 373 then (i + 702) else (i + 537))) else (if i < 376 then (i + 693) else (if i < 377 then (i + 733) else (i + 537)))))))) else (if i < 502 then (if i < 444 then (if i < 404 then (if i < 388 then (if i < 384 then (if i < 381 then (i + 686) else (i + 537)) else (if i < 385 then (i + 747) else (if i < 387 then (i + 537) else (i + 712)))) else (if i < 401 then (if i < 400 then (i + 537) else (i + 733)) else (if i < 402 then (i + 737) else (if i < 403 then (i + 695) else (i + 700))))) else (if i < 422 then (if i < 418 then (if i < 417 then (i + 535) else (i + 710)) else (if i < 420 then (i + 535) else (if i < 421 then (i + 667) else (i + 670)))) else (if i < 431 then (if i < 430 then (i + 535) else (i + 655)) else (if i < 432 then (i + 658) else (if i < 433 then (i + 693) else (i + 535)))))) else (if i < 490 then (if i < 484 then (if i < 481 then (if i < 446 then (i + 1) else (i + 533)) else (if i < 482 then (i + 534) else (if i < 483 then (i + 535) else (i + 536)))) else (if i < 487 then (if i < 486 then (i + 537) else (i + 538)) else (if i < 488 then (i + 539) else (if i < 489 then (i + 540) else (i + 541))))) else (if i < 496 then (if i < 493 then (if i < 492 then (i + 542) else (i + 543)) else (if i < 494 then (i + 544) else (if i < 495 then (i + 545) else (i + 546)))) else (if i < 499 then (if i < 497 then (i + 547) else (if i < 498 then (i + 548) else (i + 549))) else (if i < 500 then (i + 550) else (if i < 501 then (i + 551) else (i + 552))))))) else (if i < 526 then (if i < 514 then (if i < 509 then (if i < 505 then (if i < 503 then (i + 553) else (i + 554)) else (if i < 507 then (i + 555) else (if i < 508 then (i + 556) else (i + 557)))) else (if i < 511 then (if i < 510 then (i + 558) else (i + 559)) else (if i < 512 then (i + 560) else (if i < 513 then (i + 561) else (i + 562))))) else (if i < 520 then (if i < 517 then (if i < 515 then (i + 563) else (i + 564)) else (if i < 518 then (i + 565) else (if i < 519 then (i + 566) else (i + 567)))) else (if i < 523 then (if i < 521 then (i + 568) else (if i < 522 then (i + 569) else (i + 570))) else (if i < 524 then (i + 571) else (if i < 525 then (i + 572) else (i + 573)))))) else (if i < 536 then (if i < 531 then (if i < 528 then (if i < 527 then (i + 574) else (i + 575)) else (if i < 529 then (i + 576) else (if i < 530 then (i + 577) else (i + 578)))) else (if i < 533 then (if i < 532 then (i + 579) else (i + 580)) else (if i < 534 then (i + 581) else (if i < 535 then (i + 582) else (i + 583))))) else (if i < 541 then (if i < 538 then (if i < 537 then (i + 584) else (i + 585)) else (if i < 539 then (i + 586) else (if i < 540 then (i + 587) else (i + 588)))) else (if i < 544 then (if i < 542 then (i + 589) else (if i < 543 then (i + 590) else (i + 591))) else (if i < 546 then (i + 592) else (if i < 548 then (i + 593) else (i + 1)))))))))

def steps : List Step := [⟨⟨148,531,[376]⟩,1110⟩,
⟨⟨149,350,[53]⟩,1111⟩,
⟨⟨149,532,[350]⟩,1112⟩,
⟨⟨150,339,[70]⟩,1113⟩,
⟨⟨150,533,[339]⟩,1114⟩,
⟨⟨151,351,[377]⟩,1115⟩,
⟨⟨151,534,[351]⟩,1116⟩,
⟨⟨152,280,[19]⟩,1117⟩,
⟨⟨152,535,[280]⟩,1118⟩,
⟨⟨153,264,[416]⟩,1119⟩,
⟨⟨153,536,[264]⟩,1120⟩,
⟨⟨154,265,[97]⟩,1121⟩,
⟨⟨154,537,[265]⟩,1122⟩,
⟨⟨155,281,[89]⟩,1123⟩,
⟨⟨155,538,[281]⟩,1124⟩,
⟨⟨156,432,[27]⟩,1125⟩,
⟨⟨156,539,[432]⟩,1126⟩,
⟨⟨157,417,[433]⟩,1127⟩,
⟨⟨157,540,[417]⟩,1128⟩,
⟨⟨158,296,[43]⟩,1129⟩,
⟨⟨158,541,[296]⟩,1130⟩,
⟨⟨159,384,[35]⟩,1131⟩,
⟨⟨159,542,[384]⟩,1132⟩,
⟨⟨37,400,[297]⟩,1133⟩,
⟨⟨37,543,[400]⟩,1134⟩,
⟨⟨160,312,[74]⟩,1135⟩,
⟨⟨160,544,[312]⟩,1136⟩,
⟨⟨45,545,[313]⟩,1137⟩,
⟨⟨76,401,[385]⟩,1138⟩,
⟨⟨76,546,[401]⟩,1139⟩,
⟨⟨59,547,[346]⟩,1140⟩,
⟨⟨67,328,[65]⟩,1141⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block014

namespace CSL.Construction.FiniteSSA.Verified.Block015
open CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev before := CSL.Construction.FiniteSSA.Verified.Block014.after

def after (i : Nat) : Nat := (if i < 388 then (if i < 321 then (if i < 269 then (if i < 243 then (if i < 233 then (if i < 223 then (if i < 111 then (i + 1) else (if i < 222 then (i + 551) else (i + 826))) else (if i < 224 then (i + 827) else (if i < 232 then (i + 551) else (i + 782)))) else (if i < 240 then (if i < 234 then (i + 551) else (if i < 235 then (i + 786) else (i + 551))) else (if i < 241 then (i + 776) else (if i < 242 then (i + 551) else (i + 776))))) else (if i < 254 then (if i < 247 then (if i < 244 then (i + 780) else (if i < 246 then (i + 549) else (i + 808))) else (if i < 252 then (i + 549) else (if i < 253 then (i + 800) else (i + 803)))) else (if i < 264 then (if i < 256 then (i + 547) else (if i < 257 then (i + 827) else (i + 547))) else (if i < 266 then (if i < 265 then (i + 855) else (i + 856)) else (if i < 268 then (i + 547) else (i + 883)))))) else (if i < 299 then (if i < 281 then (if i < 273 then (if i < 270 then (i + 886) else (if i < 272 then (i + 547) else (i + 809))) else (if i < 279 then (i + 547) else (if i < 280 then (i + 878) else (i + 837)))) else (if i < 287 then (if i < 282 then (i + 842) else (if i < 286 then (i + 547) else (i + 809))) else (if i < 297 then (if i < 296 then (i + 547) else (i + 833)) else (if i < 298 then (i + 547) else (i + 865))))) else (if i < 313 then (if i < 309 then (if i < 300 then (i + 866) else (if i < 308 then (i + 547) else (i + 785))) else (if i < 310 then (i + 792) else (if i < 312 then (i + 547) else (i + 823)))) else (if i < 316 then (if i < 314 then (i + 547) else (if i < 315 then (i + 855) else (i + 856))) else (if i < 319 then (if i < 318 then (i + 547) else (i + 709)) else (if i < 320 then (i + 547) else (i + 716))))))) else (if i < 352 then (if i < 337 then (if i < 327 then (if i < 324 then (if i < 322 then (i + 717) else (if i < 323 then (i + 547) else (i + 721))) else (if i < 325 then (i + 701) else (if i < 326 then (i + 706) else (i + 781)))) else (if i < 330 then (if i < 328 then (i + 545) else (if i < 329 then (i + 813) else (i + 814))) else (if i < 334 then (i + 543) else (if i < 336 then (i + 1) else (i + 706))))) else (if i < 344 then (if i < 340 then (if i < 338 then (i + 709) else (if i < 339 then (i + 767) else (i + 774))) else (if i < 341 then (i + 541) else (if i < 342 then (i + 693) else (i + 541)))) else (if i < 348 then (if i < 345 then (i + 685) else (if i < 347 then (i + 541) else (i + 800))) else (if i < 350 then (if i < 349 then (i + 692) else (i + 541)) else (if i < 351 then (i + 761) else (i + 764)))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (i + 541) else (if i < 355 then (i + 705) else (i + 707))) else (if i < 357 then (i + 714) else (if i < 359 then (i + 539) else (i + 705)))) else (if i < 364 then (if i < 361 then (i + 539) else (if i < 362 then (i + 717) else (i + 539))) else (if i < 366 then (if i < 365 then (i + 781) else (i + 539)) else (if i < 367 then (i + 706) else (i + 709))))) else (if i < 376 then (if i < 372 then (if i < 369 then (i + 537) else (if i < 370 then (i + 780) else (i + 537))) else (if i < 373 then (i + 702) else (if i < 375 then (i + 537) else (i + 693)))) else (if i < 381 then (if i < 377 then (i + 733) else (if i < 380 then (i + 537) else (i + 686))) else (if i < 385 then (if i < 384 then (i + 537) else (i + 747)) else (if i < 387 then (i + 537) else (i + 712)))))))) else (if i < 510 then (if i < 446 then (if i < 420 then (if i < 403 then (if i < 400 then (if i < 397 then (i + 537) else (if i < 398 then (i + 776) else (i + 537))) else (if i < 401 then (i + 733) else (if i < 402 then (i + 737) else (i + 695)))) else (if i < 407 then (if i < 404 then (i + 700) else (if i < 406 then (i + 535) else (i + 761))) else (if i < 417 then (i + 535) else (if i < 418 then (i + 710) else (i + 535))))) else (if i < 430 then (if i < 426 then (if i < 421 then (i + 667) else (if i < 422 then (i + 670) else (i + 535))) else (if i < 427 then (i + 727) else (if i < 428 then (i + 734) else (i + 535)))) else (if i < 433 then (if i < 431 then (i + 655) else (if i < 432 then (i + 658) else (i + 693))) else (if i < 443 then (if i < 442 then (i + 535) else (i + 717)) else (if i < 444 then (i + 535) else (i + 1)))))) else (if i < 495 then (if i < 487 then (if i < 483 then (if i < 481 then (i + 533) else (if i < 482 then (i + 534) else (i + 535))) else (if i < 484 then (i + 536) else (if i < 486 then (i + 537) else (i + 538)))) else (if i < 490 then (if i < 488 then (i + 539) else (if i < 489 then (i + 540) else (i + 541))) else (if i < 493 then (if i < 492 then (i + 542) else (i + 543)) else (if i < 494 then (i + 544) else (i + 545))))) else (if i < 501 then (if i < 498 then (if i < 496 then (i + 546) else (if i < 497 then (i + 547) else (i + 548))) else (if i < 499 then (i + 549) else (if i < 500 then (i + 550) else (i + 551)))) else (if i < 505 then (if i < 502 then (i + 552) else (if i < 503 then (i + 553) else (i + 554))) else (if i < 508 then (if i < 507 then (i + 555) else (i + 556)) else (if i < 509 then (i + 557) else (i + 558))))))) else (if i < 537 then (if i < 524 then (if i < 517 then (if i < 513 then (if i < 511 then (i + 559) else (if i < 512 then (i + 560) else (i + 561))) else (if i < 514 then (i + 562) else (if i < 515 then (i + 563) else (i + 564)))) else (if i < 520 then (if i < 518 then (i + 565) else (if i < 519 then (i + 566) else (i + 567))) else (if i < 522 then (if i < 521 then (i + 568) else (i + 569)) else (if i < 523 then (i + 570) else (i + 571))))) else (if i < 530 then (if i < 527 then (if i < 525 then (i + 572) else (if i < 526 then (i + 573) else (i + 574))) else (if i < 528 then (i + 575) else (if i < 529 then (i + 576) else (i + 577)))) else (if i < 533 then (if i < 531 then (i + 578) else (if i < 532 then (i + 579) else (i + 580))) else (if i < 535 then (if i < 534 then (i + 581) else (i + 582)) else (if i < 536 then (i + 583) else (i + 584)))))) else (if i < 552 then (if i < 543 then (if i < 540 then (if i < 538 then (i + 585) else (if i < 539 then (i + 586) else (i + 587))) else (if i < 541 then (i + 588) else (if i < 542 then (i + 589) else (i + 590)))) else (if i < 548 then (if i < 544 then (i + 591) else (if i < 546 then (i + 592) else (i + 593))) else (if i < 550 then (if i < 549 then (i + 594) else (i + 595)) else (if i < 551 then (i + 596) else (i + 597))))) else (if i < 558 then (if i < 555 then (if i < 553 then (i + 598) else (if i < 554 then (i + 599) else (i + 600))) else (if i < 556 then (i + 601) else (if i < 557 then (i + 602) else (i + 603)))) else (if i < 561 then (if i < 559 then (i + 604) else (if i < 560 then (i + 605) else (i + 606))) else (if i < 563 then (if i < 562 then (i + 607) else (i + 608)) else (if i < 564 then (i + 609) else (i + 1)))))))))

def steps : List Step := [⟨⟨67,548,[328]⟩,1142⟩,
⟨⟨68,329,[66]⟩,1143⟩,
⟨⟨68,549,[329]⟩,1144⟩,
⟨⟨161,364,[57]⟩,1145⟩,
⟨⟨161,550,[364]⟩,1146⟩,
⟨⟨162,347,[368]⟩,1147⟩,
⟨⟨162,551,[347]⟩,1148⟩,
⟨⟨163,369,[365]⟩,1149⟩,
⟨⟨163,552,[369]⟩,1150⟩,
⟨⟨164,268,[278]⟩,1151⟩,
⟨⟨164,553,[268]⟩,1152⟩,
⟨⟨165,426,[21]⟩,1153⟩,
⟨⟨165,554,[426]⟩,1154⟩,
⟨⟨166,269,[102]⟩,1155⟩,
⟨⟨166,555,[269]⟩,1156⟩,
⟨⟨167,279,[94]⟩,1157⟩,
⟨⟨167,556,[279]⟩,1158⟩,
⟨⟨168,442,[26]⟩,1159⟩,
⟨⟨168,557,[442]⟩,1160⟩,
⟨⟨169,427,[443]⟩,1161⟩,
⟨⟨169,558,[427]⟩,1162⟩,
⟨⟨170,298,[44]⟩,1163⟩,
⟨⟨170,559,[298]⟩,1164⟩,
⟨⟨171,299,[396]⟩,1165⟩,
⟨⟨171,560,[299]⟩,1166⟩,
⟨⟨172,406,[36]⟩,1167⟩,
⟨⟨172,561,[406]⟩,1168⟩,
⟨⟨173,314,[80]⟩,1169⟩,
⟨⟨173,562,[314]⟩,1170⟩,
⟨⟨174,315,[84]⟩,1171⟩,
⟨⟨174,563,[315]⟩,1172⟩,
⟨⟨175,397,[407]⟩,1173⟩]

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
end CSL.Construction.FiniteSSA.Verified.Block015


