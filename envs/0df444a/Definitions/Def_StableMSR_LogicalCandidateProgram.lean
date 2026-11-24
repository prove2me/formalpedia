-- Prove2me | Definitions.Def_StableMSR_LogicalCandidateProgram
-- name    : StableMSR_LogicalCandidateProgram
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T02:13:28.028933+00:00
-- url     : https://prove2.me/theorems/36c61d56-4adb-4f50-bca3-c4c056669dfe
-- title:
--   Source semantics for the fixed sum-of-radii candidate enumerator
-- statement:
--   An integer source program with separate immutable input, scratch array and an append-only stream of typed records. Arithmetic, allocation, emission and control flow have explicit charges in interpreter steps. Lowering expands each source operation into the corresponding register-machine routine. The specified program has an explicit definition for every geometry and candidate-enumeration subroutine.
-- source:
--   Ravichandran and Reyzin, Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
/-- The source machine never exposes the temporaries of the arithmetic macros
or the temporary registers private to the record writer. -/
def visible (j:ℕ):Bool := decide (j < 10 ∨ 15 < j) && decide (j≠221) && decide (j < 861 ∨ 903 < j)
def rawInput (q:ℤ):Bool := decide (0 ≤ q) || (decide (q ≤  -87) && decide ((-87-q)%64=0))

structure State where
  reg : ℕ → ℤ
  heap : ℕ → ℤ
  output : List Instr
  closed : Bool
def initial (s:Banks) : State := ⟨s.reg,fun i=>s.mem (cell 7 i),[],false⟩
def State.assign (s:State) (d:ℕ) (a:ℤ) := {s with reg:=Function.update s.reg d a}
def State.clear (s:State) (base len:ℕ) := {s with heap:=fun i=>if base ≤ i ∧ i < base+len then 0 else s.heap i}
def State.save (s:State) (i:ℕ) (v:ℤ) := {s with heap:=Function.update s.heap i v}

inductive Operation where
  | regular (o:IOp) | multiply (d a b:ℕ) | divide (quot:Bool) (d a b:ℕ)
  | shift (d a k:ℕ) | fetch (d a i:ℕ) | save (a i v:ℕ) | alloc (d len:ℕ) | output

def Operation.lower : Operation → Code
  | .regular o=>.atom o | .multiply d a b=>mul d a b | .divide q d a b=>divrem q d a b
  | .shift d a k=>lshift d a k | .fetch d a i=>readCell d a i | .save a i v=>writeCell a i v
  | .alloc d l=>allocate d l | .output=>proc_output

def IRegular (o:IOp) : Bool:=match o with
  | .set d _|.inc d|.dec d=>visible d
  | .copy d a|.load d a|.store d a=>visible d && visible a
  | .add d a b|.sub d a b=>visible d && visible a && visible b
def high (a:ℕ):Bool:=visible a && decide (64 ≤ a)
def Operation.safe : Operation → Bool
  | .regular o=>IRegular o | .multiply d a b=>high d && high a && high b && decide (a≠d)
  | .divide _ d a b=>high d && high a && high b
  | .shift d a _=>visible d && visible a
  | .fetch d a i|.save d a i=>high d && high a && high i
  | .alloc d l=>high d && high l && decide (d≠l) | .output=>true

def record (n:ℕ) (s:State) : Instr :=
  let t:=s.reg 218
  let a:=s.reg 219
  if t=0 then .lit ((List.range n).filter (fun j=>s.heap ((s.reg 220).toNat+j)==1))
  else if t=1 then .need a.toNat else if t=2 then .close (a==1)
  else if t=3 then .seal a.toNat else .finish
def State.bitsOK (s:State) (n:ℕ) (e:Instr) : Bool := match e with
  | .lit _=>decide (0 ≤ s.reg 220) && (List.range n).all (fun j=>let v:=s.heap ((s.reg 220).toNat+j); v==0 || v==1)
  | _=>true

def regularNext (input:ℤ → ℤ) (s:State) : IOp → Option (State×ℕ)
  | .set d v=>some (s.assign d v,1)
  | .copy d a=>some (s.assign d (s.reg a),1)
  | .inc d=>some (s.assign d (s.reg d+1),1)
  | .dec d=>some (s.assign d (s.reg d-1),1)
  | .add d a b=>some (s.assign d (s.reg a+s.reg b),1)
  | .sub d a b=>some (s.assign d (s.reg a-s.reg b),1)
  | .load d a=>if rawInput (s.reg a) then some (s.assign d (input (s.reg a)),1) else none
  | .store a v=>if s.reg a=inputCell 0 0 ∧ s.reg v=(s.output.length:ℤ)
      then some ({s with closed:=true},1) else none

/-- A source step uses exact integer arithmetic and a separate scratch array.
Its charge bounds inspections of the compiled register code. -/
def Operation.next (n:ℕ) (input:ℤ → ℤ) (s:State) : Operation → Option (State×ℕ)
  | .regular o=>regularNext input s o
  | .multiply d a b=>if s.reg 6=1 ∧ 0 ≤ s.reg a ∧ 0 ≤ s.reg b
      then some (s.assign d (s.reg a*s.reg b),8+6*(s.reg b).toNat) else none
  | .divide q d a b=>if s.reg 6=1 ∧ 0 ≤ s.reg a ∧ 0 < s.reg b then
      let A:=(s.reg a).toNat
      let B:=(s.reg b).toNat
      some (s.assign d ((if q then A/B else A%B:ℕ):ℤ),20+8*(A/B))
    else none
  | .shift d a k=>some (s.assign d ((2:ℤ)^k*s.reg a),3+2*k)
  | .fetch d a i=>let j:=s.reg a+s.reg i
    if 0 ≤ j then some (s.assign d (s.heap j.toNat),64) else none
  | .save a i v=>let j:=s.reg a+s.reg i
    if 0 ≤ j then some (s.save j.toNat (s.reg v),64) else none
  | .alloc d len=>if s.reg 6=1 ∧ s.reg 7=0 ∧ 0 ≤ s.reg 8 ∧ 0 ≤ s.reg len then
      let a:=(s.reg 8).toNat
      let l:=(s.reg len).toNat
      some (((s.clear a l).assign d a |>.assign 8 (a+l:ℕ)),64*(1+l))
    else none
  | .output=>
    let e:=record n s
    if s.closed=false ∧ s.reg 6=1 ∧ s.reg 64=(n:ℤ) ∧ s.reg 82=(s.output.length:ℤ) ∧
        s.reg 218=e.tag ∧ s.reg 219=e.arg ∧ s.bitsOK n e=true then
      some ({(s.assign 82 (s.reg 82+1)) with output:=s.output++[e]},200+n*(165+6*n))
    else none

inductive Program where
  | skip | op (o:Operation) | seq (a b:Program)
  | cond (a b:ℕ) (yes no:Program) | loop (a b:ℕ) (p:Program)
def Program.lower : Program → Code
  | .skip=>.skip | .op o=>o.lower | .seq p q=>.seq p.lower q.lower
  | .cond a b p q=>.cond a b p.lower q.lower | .loop a b p=>.loop a b p.lower
def Program.safe : Program → Bool
  | .skip=>true | .op o=>o.safe | .seq p q=>p.safe && q.safe
  | .cond a b p q=>visible a && visible b && p.safe && q.safe
  | .loop a b p=>visible a && visible b && p.safe
def chain (ps:List Program) := ps.foldr Program.seq Program.skip
def forCount (i last len:ℕ) (p:Program) := chain [
  .op (.regular (.set i 0)),.op (.regular (.copy last len)),.op (.regular (.dec last)),
  .loop i last (chain [p,.op (.regular (.inc i))])]

/-- Big-step semantics of the source loop program; the cost is in compiled
syntax inspections and includes all sequence and branch bookkeeping. -/
inductive Executes (n:ℕ) (input:ℤ → ℤ) : Program → State → State → ℕ → Prop where
  | skip (s:State) : Executes n input .skip s s 1
  | op {o s t k} : o.next n input s=some (t,k)  →  Executes n input (.op o) s t k
  | seq {p q s t u a b} : Executes n input p s t a  →  Executes n input q t u b  →  Executes n input (.seq p q) s u (1+a+b)
  | yes {i j p q s t a} : s.reg i  ≤  s.reg j  →  Executes n input p s t a  →  Executes n input (.cond i j p q) s t (1+a)
  | no {i j p q s t a} : ¬s.reg i  ≤  s.reg j  →  Executes n input q s t a  →  Executes n input (.cond i j p q) s t (1+a)
  | stop {i j p s} : ¬s.reg i  ≤  s.reg j  →  Executes n input (.loop i j p) s s 1
  | more {i j p s t u a b} : s.reg i  ≤  s.reg j  →  Executes n input p s t a  →  Executes n input (.loop i j p) t u b  → 
    Executes n input (.loop i j p) s u (1+a+b)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
/-- Source operations of code_name_push. -/
def src_code_name_push : Program :=
  chain [.op (.shift 275 128 1),
  .op (.regular (.set 277 1)),
  .op (.regular (.add 274 275 277)),
  .op (.regular (.copy 128 274)),
  forCount 130 279 129 (chain [.op (.regular (.add 280 128 128)),
      .op (.regular (.copy 128 280))]),
  .op (.regular (.copy 131 128))]

/-- Source operations of component. -/
def src_component : Program :=
  chain [.op (.alloc 284 64),
  .op (.regular (.copy 134 284)),
  .op (.regular (.set 289 1)),
  .op (.save 134 133 289),
  forCount 135 291 64 (forCount 136 293 64 (chain [.op (.fetch 295 132 136),
        .op (.regular (.copy 294 295)),
        .cond 6 294 (chain [.op (.fetch 299 134 136),
            .cond 6 299 (.op (.regular (.set 298 0))) (.op (.regular (.set 298 1))),
            .op (.regular (.copy 294 298))]) (.skip),
        .cond 6 294 (forCount 137 303 64 (chain [.op (.fetch 305 134 137),
              .op (.regular (.copy 304 305)),
              .cond 6 304 (chain [.op (.multiply 311 137 64),
                  .op (.regular (.add 310 311 136)),
                  .op (.fetch 308 75 310),
                  .op (.regular (.copy 304 308))]) (.skip),
              .cond 6 304 (chain [.op (.regular (.set 318 1)),
                  .op (.save 134 136 318)]) (.skip)])) (.skip)])),
  .op (.regular (.copy 138 134))]

/-- Source operations of rim. -/
def src_rim : Program :=
  chain [.op (.alloc 320 64),
  .op (.regular (.copy 140 320)),
  forCount 141 323 64 (chain [.op (.fetch 325 71 141),
      .op (.regular (.copy 324 325)),
      .cond 6 324 (chain [.op (.fetch 329 139 141),
          .cond 6 329 (.op (.regular (.set 328 0))) (.op (.regular (.set 328 1))),
          .op (.regular (.copy 324 328))]) (.skip),
      .cond 6 324 (forCount 142 333 64 (chain [.op (.fetch 335 139 142),
            .op (.regular (.copy 334 335)),
            .cond 6 334 (chain [.op (.multiply 341 142 64),
                .op (.regular (.add 340 341 141)),
                .op (.fetch 338 75 340),
                .op (.regular (.copy 334 338))]) (.skip),
            .cond 6 334 (chain [.op (.regular (.set 348 1)),
                .op (.save 140 141 348)]) (.skip)])) (.skip)]),
  .op (.regular (.copy 143 140))]

/-- Source operations of first. -/
def src_first : Program :=
  chain [.op (.regular (.copy 145 64)),
  forCount 146 352 64 (chain [.op (.fetch 354 144 146),
      .op (.regular (.copy 353 354)),
      .cond 6 353 (chain [.cond 145 146 (.op (.regular (.set 357 0))) (.op (.regular (.set 357 1))),
          .op (.regular (.copy 353 357))]) (.skip),
      .cond 6 353 (.op (.regular (.copy 145 146))) (.skip)]),
  .op (.regular (.copy 147 145))]

/-- Source operations of equal_rows. -/
def src_equal_rows : Program :=
  chain [.op (.regular (.set 362 1)),
  .op (.regular (.copy 150 362)),
  forCount 151 364 64 (chain [.op (.fetch 366 148 151),
      .op (.fetch 369 149 151),
      .cond 366 369 (.cond 369 366 (.op (.regular (.set 365 0))) (.op (.regular (.set 365 1)))) (.op (.regular (.set 365 1))),
      .cond 6 365 (chain [.op (.regular (.set 372 0)),
          .op (.regular (.copy 150 372))]) (.skip)]),
  .op (.regular (.copy 152 150))]

/-- Source operations of name_key. -/
def src_name_key : Program :=
  chain [.op (.regular (.set 374 0)),
  .op (.regular (.copy 156 374)),
  forCount 157 376 64 (chain [.op (.fetch 377 153 157),
      .cond 6 377 (chain [.op (.regular (.set 384 1)),
          .op (.regular (.add 382 157 384)),
          .op (.regular (.copy 128 156)),
          .op (.regular (.copy 129 382)),
          src_code_name_push,
          .op (.regular (.copy 380 131)),
          .op (.regular (.copy 156 380))]) (.skip)]),
  .op (.regular (.set 387 0)),
  .op (.regular (.copy 128 156)),
  .op (.regular (.copy 129 387)),
  src_code_name_push,
  .op (.regular (.copy 385 131)),
  .op (.regular (.copy 156 385)),
  forCount 157 389 64 (chain [.op (.fetch 390 154 157),
      .cond 6 390 (chain [.op (.regular (.copy 128 156)),
          .op (.regular (.copy 129 157)),
          src_code_name_push,
          .op (.regular (.copy 393 131)),
          .op (.regular (.copy 156 393)),
          .op (.fetch 400 155 157),
          .op (.fetch 398 76 400),
          .op (.regular (.copy 128 156)),
          .op (.regular (.copy 129 398)),
          src_code_name_push,
          .op (.regular (.copy 396 131)),
          .op (.regular (.copy 156 396))]) (.skip)]),
  .op (.regular (.copy 158 156))]

/-- Source operations of imat. -/
def src_imat : Program :=
  chain [.op (.regular (.set 407 0)),
  .op (.regular (.set 408 87)),
  .op (.regular (.sub 406 407 408)),
  .op (.multiply 411 159 64),
  .op (.regular (.add 410 411 160)),
  .op (.shift 409 410 6),
  .op (.regular (.sub 405 406 409)),
  .op (.regular (.load 404 405)),
  .op (.regular (.copy 161 404))]

/-- Source operations of data_for_vertex. -/
def src_data_for_vertex : Program :=
  chain [.op (.multiply 417 162 70),
  .op (.regular (.add 416 417 164)),
  .op (.multiply 415 416 64),
  .op (.regular (.copy 165 415)),
  .op (.shift 423 68 1),
  .op (.alloc 422 423),
  .op (.regular (.copy 166 422)),
  .op (.divide true 425 163 68),
  .op (.regular (.copy 167 425)),
  .op (.shift 428 68 1),
  forCount 168 430 428 (chain [.op (.divide false 434 167 64),
      .op (.save 166 168 434),
      .op (.divide true 437 167 64),
      .op (.regular (.copy 167 437))]),
  .op (.divide false 440 163 68),
  .op (.regular (.copy 169 440)),
  .op (.multiply 445 162 64),
  .op (.regular (.add 443 74 445)),
  .op (.regular (.copy 170 443)),
  .op (.alloc 448 64),
  .op (.regular (.copy 171 448)),
  .op (.regular (.set 450 1)),
  .op (.regular (.copy 172 450)),
  forCount 173 452 64 (chain [.op (.fetch 453 170 173),
      .cond 6 453 (chain [.op (.regular (.add 459 165 173)),
          .op (.multiply 458 459 64),
          .op (.regular (.add 456 80 458)),
          .op (.regular (.copy 176 456)),
          forCount 174 464 64 (chain [.op (.fetch 465 170 174),
              .cond 6 465 (chain [.op (.regular (.set 468 0)),
                  .op (.regular (.copy 180 468)),
                  .op (.regular (.set 469 0)),
                  .op (.regular (.copy 181 469)),
                  .op (.regular (.set 470 0)),
                  .op (.regular (.copy 182 470)),
                  forCount 183 472 169 (chain [.op (.regular (.set 478 1)),
                    .op (.regular (.add 476 183 478)),
                    .op (.shift 475 476 1),
                    .op (.fetch 473 166 475),
                    .op (.regular (.copy 178 473)),
                    .op (.regular (.set 485 1)),
                    .op (.regular (.add 483 183 485)),
                    .op (.shift 482 483 1),
                    .op (.regular (.set 486 1)),
                    .op (.regular (.add 481 482 486)),
                    .op (.fetch 479 166 481),
                    .op (.regular (.copy 184 479)),
                    .op (.regular (.copy 159 178)),
                    .op (.regular (.copy 160 184)),
                    src_imat,
                    .op (.regular (.copy 487 161)),
                    .op (.regular (.copy 185 487)),
                    .op (.regular (.copy 159 178)),
                    .op (.regular (.copy 160 173)),
                    src_imat,
                    .op (.regular (.copy 491 161)),
                    .cond 491 185 (.op (.regular (.set 490 1))) (.op (.regular (.set 490 0))),
                    .op (.regular (.copy 186 490)),
                    .op (.regular (.copy 159 178)),
                    .op (.regular (.copy 160 174)),
                    src_imat,
                    .op (.regular (.copy 496 161)),
                    .cond 496 185 (.op (.regular (.set 495 1))) (.op (.regular (.set 495 0))),
                    .op (.regular (.copy 187 495)),
                    .cond 6 186 (chain [.op (.regular (.set 501 1)),
                    .op (.regular (.copy 181 501))]) (.skip),
                    .cond 6 187 (chain [.op (.regular (.set 503 1)),
                    .op (.regular (.copy 182 503))]) (.skip),
                    .op (.regular (.copy 504 186)),
                    .cond 6 504 (.op (.regular (.copy 504 187))) (.skip),
                    .cond 6 504 (chain [.op (.regular (.set 507 1)),
                    .op (.regular (.copy 180 507))]) (.skip)]),
                  .cond 6 181 (.op (.regular (.set 509 0))) (.op (.regular (.set 509 1))),
                  .op (.regular (.copy 508 509)),
                  .cond 6 508 (chain [.cond 6 182 (.op (.regular (.set 511 0))) (.op (.regular (.set 511 1))),
                    .op (.regular (.copy 508 511))]) (.skip),
                  .cond 6 508 (chain [.op (.regular (.copy 159 173)),
                    .op (.regular (.copy 160 174)),
                    src_imat,
                    .op (.regular (.copy 514 161)),
                    .op (.regular (.set 520 0)),
                    .op (.fetch 518 166 520),
                    .op (.regular (.set 523 1)),
                    .op (.fetch 521 166 523),
                    .op (.regular (.copy 159 518)),
                    .op (.regular (.copy 160 521)),
                    src_imat,
                    .op (.regular (.copy 517 161)),
                    .cond 514 517 (.op (.regular (.set 513 1))) (.op (.regular (.set 513 0))),
                    .cond 6 513 (chain [.op (.regular (.set 524 1)),
                    .op (.regular (.copy 180 524))]) (.skip)]) (.skip),
                  .op (.save 176 174 180)]) (.skip)]),
          .op (.regular (.set 529 1)),
          .op (.regular (.copy 177 529)),
          forCount 178 531 173 (chain [.op (.fetch 533 171 178),
              .op (.regular (.copy 532 533)),
              .cond 6 532 (chain [.op (.regular (.add 541 165 178)),
                  .op (.multiply 540 541 64),
                  .op (.regular (.add 538 80 540)),
                  .op (.regular (.copy 148 176)),
                  .op (.regular (.copy 149 538)),
                  src_equal_rows,
                  .op (.regular (.copy 536 152)),
                  .op (.regular (.copy 532 536))]) (.skip),
              .cond 6 532 (chain [.op (.regular (.set 545 0)),
                  .op (.regular (.copy 177 545))]) (.skip)]),
          .cond 6 177 (chain [.op (.regular (.set 550 1)),
              .op (.save 171 173 550),
              .op (.regular (.add 553 165 173)),
              .op (.regular (.set 556 1)),
              .op (.save 77 553 556),
              .op (.regular (.copy 144 176)),
              src_first,
              .op (.regular (.copy 557 147)),
              .op (.regular (.copy 179 557)),
              .cond 179 64 (.cond 64 179 (.op (.regular (.set 559 1))) (.op (.regular (.set 559 0)))) (.op (.regular (.set 559 0))),
              .cond 6 559 (chain [.op (.regular (.set 562 0)),
                  .op (.regular (.copy 172 562))]) (chain [.op (.regular (.add 565 165 173)),
                  .op (.save 78 565 179),
                  forCount 174 570 64 (chain [.op (.fetch 572 176 174),
                    .op (.regular (.copy 571 572)),
                    .cond 6 571 (chain [.op (.fetch 576 72 174),
                    .cond 576 162 (.cond 162 576 (.op (.regular (.set 575 1))) (.op (.regular (.set 575 0)))) (.op (.regular (.set 575 0))),
                    .op (.regular (.copy 571 575))]) (.skip),
                    .cond 6 571 (chain [.op (.regular (.add 582 165 173)),
                    .op (.regular (.set 585 1)),
                    .op (.save 79 582 585)]) (.skip)])])]) (.skip)]) (.skip)]),
  forCount 174 587 64 (chain [.op (.regular (.set 588 0)),
      .op (.regular (.copy 175 588)),
      forCount 173 590 64 (chain [.op (.fetch 592 171 173),
          .op (.regular (.copy 591 592)),
          .cond 6 591 (chain [.op (.regular (.add 599 165 173)),
              .op (.multiply 598 599 64),
              .op (.regular (.add 597 598 174)),
              .op (.fetch 595 80 597),
              .op (.regular (.copy 591 595))]) (.skip),
          .cond 6 591 (chain [.op (.regular (.set 606 1)),
              .op (.regular (.add 604 175 606)),
              .op (.regular (.copy 175 604))]) (.skip)]),
      .op (.fetch 609 170 174),
      .cond 175 609 (.cond 609 175 (.op (.regular (.set 607 0))) (.op (.regular (.set 607 1)))) (.op (.regular (.set 607 1))),
      .cond 6 607 (chain [.op (.regular (.set 612 0)),
          .op (.regular (.copy 172 612))]) (.skip)]),
  .op (.multiply 616 162 70),
  .op (.regular (.add 615 616 164)),
  .op (.save 81 615 172)]

/-- Source operations of build_geometry. -/
def src_build_geometry : Program :=
  chain [.op (.divide true 621 65 64),
  .op (.regular (.copy 189 621)),
  .op (.divide false 624 65 64),
  .op (.regular (.copy 190 624)),
  .op (.regular (.set 629 3)),
  .op (.regular (.set 634 2)),
  .op (.regular (.add 632 64 634)),
  .op (.multiply 630 189 632),
  .op (.regular (.add 628 629 630)),
  .op (.regular (.set 635 2)),
  .op (.regular (.add 627 628 635)),
  .op (.regular (.copy 191 627)),
  .op (.regular (.add 637 191 190)),
  .op (.regular (.load 636 637)),
  .op (.regular (.copy 192 636)),
  .op (.regular (.set 640 1)),
  .op (.regular (.copy 193 640)),
  forCount 194 642 190 (chain [.op (.regular (.add 645 191 194)),
      .op (.regular (.load 644 645)),
      .cond 644 192 (.cond 192 644 (.op (.regular (.set 643 1))) (.op (.regular (.set 643 0)))) (.op (.regular (.set 643 0))),
      .cond 6 643 (chain [.op (.regular (.set 649 0)),
          .op (.regular (.copy 193 649))]) (.skip)]),
  .op (.multiply 651 64 64),
  .op (.regular (.set 654 1)),
  .op (.regular (.add 650 651 654)),
  .op (.regular (.copy 195 650)),
  forCount 194 656 64 (chain [.op (.regular (.copy 657 193)),
      .cond 6 657 (chain [.op (.regular (.add 661 191 194)),
          .op (.regular (.load 660 661)),
          .cond 660 192 (.cond 192 660 (.op (.regular (.set 659 1))) (.op (.regular (.set 659 0)))) (.op (.regular (.set 659 0))),
          .op (.regular (.copy 657 659))]) (.skip),
      .cond 6 657 (chain [.op (.regular (.set 668 1)),
          .op (.save 73 194 668),
          .op (.regular (.set 669 1)),
          .op (.regular (.copy 201 669)),
          forCount 198 671 194 (chain [.op (.fetch 673 71 198),
              .op (.regular (.copy 672 673)),
              .cond 6 672 (chain [.op (.regular (.copy 159 194)),
                  .op (.regular (.copy 160 198)),
                  src_imat,
                  .op (.regular (.copy 677 161)),
                  .op (.shift 680 195 1),
                  .cond 677 680 (.op (.regular (.set 676 1))) (.op (.regular (.set 676 0))),
                  .op (.regular (.copy 672 676))]) (.skip),
              .cond 6 672 (chain [.op (.regular (.set 682 0)),
                  .op (.regular (.copy 201 682))]) (.skip)]),
          .op (.save 71 194 201)]) (.skip)]),
  forCount 194 688 64 (chain [.op (.regular (.copy 197 64)),
      forCount 198 691 64 (chain [.op (.fetch 693 71 198),
          .op (.regular (.copy 692 693)),
          .cond 6 692 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 697 161)),
              .op (.shift 700 195 1),
              .cond 697 700 (.op (.regular (.set 696 1))) (.op (.regular (.set 696 0))),
              .op (.regular (.copy 692 696))]) (.skip),
          .cond 6 692 (chain [.cond 197 198 (.op (.regular (.set 702 0))) (.op (.regular (.set 702 1))),
              .op (.regular (.copy 692 702))]) (.skip),
          .cond 6 692 (.op (.regular (.copy 197 198))) (.skip)]),
      .cond 197 64 (.cond 64 197 (.op (.regular (.set 706 1))) (.op (.regular (.set 706 0)))) (.op (.regular (.set 706 0))),
      .cond 6 706 (.op (.regular (.copy 197 194))) (.skip),
      .op (.save 72 194 197),
      forCount 198 715 64 (chain [.op (.fetch 717 73 194),
          .op (.regular (.copy 716 717)),
          .cond 6 716 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 721 161)),
              .op (.shift 724 195 2),
              .cond 721 724 (.op (.regular (.set 720 1))) (.op (.regular (.set 720 0))),
              .op (.regular (.copy 716 720))]) (.skip),
          .cond 6 716 (chain [.op (.multiply 729 198 64),
              .op (.regular (.add 728 729 194)),
              .op (.regular (.set 733 1)),
              .op (.save 74 728 733)]) (.skip),
          .cond 194 198 (.cond 198 194 (.op (.regular (.set 735 0))) (.op (.regular (.set 735 1)))) (.op (.regular (.set 735 1))),
          .op (.regular (.copy 734 735)),
          .cond 6 734 (chain [.op (.regular (.copy 159 194)),
              .op (.regular (.copy 160 198)),
              src_imat,
              .op (.regular (.copy 739 161)),
              .op (.shift 742 195 3),
              .cond 739 742 (.op (.regular (.set 738 1))) (.op (.regular (.set 738 0))),
              .op (.regular (.copy 734 738))]) (.skip),
          .cond 6 734 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 745 161)),
              .op (.shift 748 195 3),
              .cond 745 748 (.op (.regular (.set 744 1))) (.op (.regular (.set 744 0))),
              .op (.regular (.copy 734 744))]) (.skip),
          .cond 6 734 (chain [.op (.multiply 753 194 64),
              .op (.regular (.add 752 753 198)),
              .op (.regular (.set 757 1)),
              .op (.save 75 752 757)]) (.skip)])]),
  forCount 196 759 70 (chain [.op (.divide false 762 196 69),
      .op (.multiply 761 762 68),
      .op (.divide true 766 196 69),
      .op (.regular (.add 760 761 766)),
      .op (.regular (.copy 199 760)),
      .op (.save 76 196 199),
      forCount 200 774 64 (chain [.op (.regular (.copy 162 200)),
          .op (.regular (.copy 163 199)),
          .op (.regular (.copy 164 196)),
          src_data_for_vertex,
          .op (.regular (.copy 775 188))])])]

/-- Source operations of fits. -/
def src_fits : Program :=
  chain [.op (.multiply 781 203 70),
  .op (.regular (.add 780 781 204)),
  .op (.multiply 779 780 64),
  .op (.regular (.copy 207 779)),
  .op (.multiply 788 205 70),
  .op (.regular (.add 787 788 206)),
  .op (.multiply 786 787 64),
  .op (.regular (.copy 208 786)),
  .op (.regular (.set 793 1)),
  .op (.regular (.copy 209 793)),
  forCount 210 795 64 (chain [.op (.regular (.add 799 207 210)),
      .op (.fetch 797 77 799),
      .op (.regular (.copy 796 797)),
      .cond 6 796 (chain [.op (.regular (.add 804 207 210)),
          .op (.fetch 802 79 804),
          .op (.regular (.copy 796 802))]) (.skip),
      .cond 6 796 (chain [.op (.regular (.add 810 207 210)),
          .op (.multiply 809 810 64),
          .op (.regular (.add 807 80 809)),
          .op (.regular (.copy 211 807)),
          forCount 212 815 64 (chain [.op (.regular (.add 819 208 212)),
              .op (.fetch 817 77 819),
              .op (.regular (.copy 816 817)),
              .cond 6 816 (chain [.op (.regular (.add 824 208 212)),
                  .op (.fetch 822 79 824),
                  .op (.regular (.copy 816 822))]) (.skip),
              .cond 6 816 (chain [.op (.regular (.add 830 208 212)),
                  .op (.multiply 829 830 64),
                  .op (.regular (.add 827 80 829)),
                  .op (.regular (.copy 213 827)),
                  .op (.regular (.set 834 0)),
                  .op (.regular (.copy 214 834)),
                  .op (.regular (.set 835 1)),
                  .op (.regular (.copy 215 835)),
                  forCount 216 837 64 (chain [.op (.fetch 839 211 216),
                    .op (.regular (.copy 838 839)),
                    .cond 6 838 (chain [.op (.fetch 842 213 216),
                    .op (.regular (.copy 838 842))]) (.skip),
                    .cond 6 838 (chain [.op (.regular (.set 845 1)),
                    .op (.regular (.copy 214 845))]) (.skip),
                    .op (.fetch 847 211 216),
                    .op (.fetch 850 213 216),
                    .cond 847 850 (.cond 850 847 (.op (.regular (.set 846 0))) (.op (.regular (.set 846 1)))) (.op (.regular (.set 846 1))),
                    .cond 6 846 (chain [.op (.regular (.set 853 0)),
                    .op (.regular (.copy 215 853))]) (.skip)]),
                  .op (.regular (.copy 854 214)),
                  .cond 6 854 (chain [.cond 6 215 (.op (.regular (.set 856 0))) (.op (.regular (.set 856 1))),
                    .op (.regular (.copy 854 856))]) (.skip),
                  .cond 6 854 (chain [.op (.regular (.set 858 0)),
                    .op (.regular (.copy 209 858))]) (.skip)]) (.skip)])]) (.skip)]),
  .op (.regular (.copy 217 209))]

/-- Source operations of trial. -/
def src_trial : Program :=
  chain [.op (.multiply 906 226 70),
  .op (.regular (.add 905 906 227)),
  .op (.multiply 904 905 64),
  .op (.regular (.copy 228 904)),
  forCount 229 912 64 (chain [.op (.fetch 914 72 229),
      .cond 914 226 (.cond 226 914 (.op (.regular (.set 913 1))) (.op (.regular (.set 913 0)))) (.op (.regular (.set 913 0))),
      .cond 6 913 (forCount 234 919 64 (chain [.op (.regular (.add 923 228 234)),
            .op (.fetch 921 77 923),
            .op (.regular (.copy 920 921)),
            .cond 6 920 (chain [.op (.regular (.add 929 228 234)),
                .op (.fetch 927 78 929),
                .cond 927 229 (.cond 229 927 (.op (.regular (.set 926 1))) (.op (.regular (.set 926 0)))) (.op (.regular (.set 926 0))),
                .op (.regular (.copy 920 926))]) (.skip),
            .cond 6 920 (chain [.op (.regular (.set 934 0)),
                .op (.regular (.set 935 0)),
                .op (.regular (.add 939 228 234)),
                .op (.multiply 938 939 64),
                .op (.regular (.add 936 80 938)),
                .op (.regular (.copy 218 934)),
                .op (.regular (.copy 219 935)),
                .op (.regular (.copy 220 936)),
                .op .output,
                .op (.regular (.copy 933 222))]) (.skip)])) (.skip)]),
  .op (.save 225 226 227),
  .op (.alloc 947 64),
  .op (.regular (.copy 230 947)),
  forCount 231 950 64 (chain [.op (.fetch 952 223 231),
      .op (.regular (.copy 951 952)),
      .cond 6 951 (chain [.cond 231 226 (.cond 226 231 (.op (.regular (.set 955 0))) (.op (.regular (.set 955 1)))) (.op (.regular (.set 955 1))),
          .op (.regular (.copy 951 955))]) (.skip),
      .cond 6 951 (chain [.op (.regular (.set 961 1)),
          .op (.save 230 231 961)]) (.skip)]),
  forCount 232 963 64 (chain [.op (.fetch 964 230 232),
      .cond 6 964 (chain [.op (.regular (.copy 132 230)),
          .op (.regular (.copy 133 232)),
          src_component,
          .op (.regular (.copy 967 138)),
          .op (.regular (.copy 235 967)),
          .op (.regular (.copy 144 235)),
          src_first,
          .op (.regular (.copy 971 147)),
          .cond 971 232 (.cond 232 971 (.op (.regular (.set 970 1))) (.op (.regular (.set 970 0)))) (.op (.regular (.set 970 0))),
          .cond 6 970 (chain [.op (.regular (.copy 139 235)),
              src_rim,
              .op (.regular (.copy 974 143)),
              .op (.regular (.copy 237 974)),
              .op (.regular (.copy 153 235)),
              .op (.regular (.copy 154 237)),
              .op (.regular (.copy 155 225)),
              src_name_key,
              .op (.regular (.copy 976 158)),
              .op (.regular (.copy 238 976)),
              .op (.regular (.set 981 1)),
              .op (.regular (.set 983 0)),
              .op (.regular (.copy 218 981)),
              .op (.regular (.copy 219 238)),
              .op (.regular (.copy 220 983)),
              .op .output,
              .op (.regular (.copy 980 222))]) (.skip)]) (.skip)]),
  .op (.regular (.set 984 1)),
  .op (.regular (.copy 233 984)),
  forCount 231 986 64 (chain [.cond 231 226 (.cond 226 231 (.op (.regular (.set 988 1))) (.op (.regular (.set 988 0)))) (.op (.regular (.set 988 0))),
      .op (.regular (.copy 987 988)),
      .cond 6 987 (.skip) (chain [.op (.fetch 991 224 231),
          .op (.regular (.copy 987 991))]),
      .cond 6 987 (forCount 236 995 64 (chain [.cond 236 226 (.cond 226 236 (.op (.regular (.set 997 1))) (.op (.regular (.set 997 0)))) (.op (.regular (.set 997 0))),
            .op (.regular (.copy 996 997)),
            .cond 6 996 (.skip) (chain [.op (.fetch 1000 224 236),
                .op (.regular (.copy 996 1000))]),
            .cond 6 996 (chain [.op (.multiply 1007 231 64),
                .op (.regular (.add 1006 1007 236)),
                .op (.fetch 1004 75 1006),
                .op (.regular (.copy 1003 1004)),
                .cond 6 1003 (chain [.op (.fetch 1014 225 231),
                    .op (.fetch 1018 225 236),
                    .op (.regular (.copy 203 231)),
                    .op (.regular (.copy 204 1014)),
                    .op (.regular (.copy 205 236)),
                    .op (.regular (.copy 206 1018)),
                    src_fits,
                    .op (.regular (.copy 1012 217)),
                    .cond 6 1012 (.op (.regular (.set 1011 0))) (.op (.regular (.set 1011 1))),
                    .op (.regular (.copy 1003 1011))]) (.skip),
                .cond 6 1003 (chain [.op (.regular (.set 1021 0)),
                    .op (.regular (.copy 233 1021))]) (.skip)]) (.skip)])) (.skip)]),
  .op (.regular (.set 1023 2)),
  .op (.regular (.set 1025 0)),
  .op (.regular (.copy 218 1023)),
  .op (.regular (.copy 219 233)),
  .op (.regular (.copy 220 1025)),
  .op .output,
  .op (.regular (.copy 1022 222)),
  .op (.regular (.set 1029 0)),
  .op (.save 225 226 1029)]

/-- Source operations of visit. -/
def src_visit : Program :=
  chain [.op (.alloc 1030 64),
  .op (.regular (.copy 244 1030)),
  forCount 245 1033 64 (chain [.op (.fetch 1035 71 245),
      .op (.regular (.copy 1034 1035)),
      .cond 6 1034 (chain [.op (.fetch 1039 241 245),
          .cond 6 1039 (.op (.regular (.set 1038 0))) (.op (.regular (.set 1038 1))),
          .op (.regular (.copy 1034 1038))]) (.skip),
      .cond 6 1034 (chain [.op (.regular (.set 1045 1)),
          .op (.save 244 245 1045)]) (.skip)]),
  forCount 246 1047 64 (chain [.op (.fetch 1048 244 246),
      .cond 6 1048 (chain [.op (.regular (.copy 132 244)),
          .op (.regular (.copy 133 246)),
          src_component,
          .op (.regular (.copy 1051 138)),
          .op (.regular (.copy 247 1051)),
          .op (.regular (.copy 144 247)),
          src_first,
          .op (.regular (.copy 1055 147)),
          .cond 1055 246 (.cond 246 1055 (.op (.regular (.set 1054 1))) (.op (.regular (.set 1054 0)))) (.op (.regular (.set 1054 0))),
          .cond 6 1054 (chain [.op (.regular (.set 1058 0)),
              .op (.regular (.copy 248 1058)),
              forCount 245 1060 64 (chain [.op (.fetch 1063 247 245),
                  .op (.regular (.add 1061 248 1063)),
                  .op (.regular (.copy 248 1061))]),
              .op (.regular (.set 1071 1)),
              .op (.regular (.add 1069 240 1071)),
              .cond 248 1069 (.cond 1069 248 (.op (.regular (.set 1067 1))) (.op (.regular (.set 1067 0)))) (.op (.regular (.set 1067 0))),
              .op (.regular (.copy 1066 1067)),
              .cond 6 1066 (chain [.op (.regular (.copy 139 247)),
                  src_rim,
                  .op (.regular (.copy 1073 143)),
                  .op (.regular (.copy 148 1073)),
                  .op (.regular (.copy 149 241)),
                  src_equal_rows,
                  .op (.regular (.copy 1072 152)),
                  .op (.regular (.copy 1066 1072))]) (.skip),
              .cond 6 1066 (chain [.op (.regular (.set 1076 1)),
                  .op (.regular (.copy 249 1076)),
                  forCount 245 1078 243 (chain [.op (.multiply 1079 249 70),
                    .op (.regular (.copy 249 1079))]),
                  .op (.alloc 1082 64),
                  .op (.regular (.copy 250 1082)),
                  forCount 251 1085 249 (chain [.op (.regular (.copy 252 251)),
                    .op (.regular (.set 1087 1)),
                    .op (.regular (.copy 253 1087)),
                    forCount 245 1089 243 (chain [.op (.regular (.set 1095 1)),
                    .op (.regular (.sub 1093 243 1095)),
                    .op (.regular (.sub 1092 1093 245)),
                    .op (.fetch 1090 242 1092),
                    .op (.regular (.copy 254 1090)),
                    .op (.divide false 1097 252 70),
                    .op (.regular (.copy 255 1097)),
                    .op (.divide true 1100 252 70),
                    .op (.regular (.copy 252 1100)),
                    .op (.save 250 254 255),
                    .op (.multiply 1111 254 70),
                    .op (.regular (.add 1110 1111 255)),
                    .op (.fetch 1108 81 1110),
                    .cond 6 1108 (.op (.regular (.set 1107 0))) (.op (.regular (.set 1107 1))),
                    .cond 6 1107 (chain [.op (.regular (.set 1115 0)),
                    .op (.regular (.copy 253 1115))]) (.skip)]),
                    .cond 6 253 (chain [forCount 256 1118 64 (chain [.op (.fetch 1119 247 256),
                    .cond 6 1119 (forCount 255 1123 70 (chain [.op (.multiply 1127 256 70),
                    .op (.regular (.add 1126 1127 255)),
                    .op (.fetch 1124 81 1126),
                    .cond 6 1124 (chain [.op (.regular (.copy 223 247)),
                    .op (.regular (.copy 224 241)),
                    .op (.regular (.copy 225 250)),
                    .op (.regular (.copy 226 256)),
                    .op (.regular (.copy 227 255)),
                    src_trial,
                    .op (.regular (.copy 1131 239))]) (.skip)])) (.skip)]),
                    .op (.regular (.copy 153 247)),
                    .op (.regular (.copy 154 241)),
                    .op (.regular (.copy 155 250)),
                    src_name_key,
                    .op (.regular (.copy 1137 158)),
                    .op (.regular (.copy 257 1137)),
                    .op (.regular (.set 1142 3)),
                    .op (.regular (.set 1144 0)),
                    .op (.regular (.copy 218 1142)),
                    .op (.regular (.copy 219 257)),
                    .op (.regular (.copy 220 1144)),
                    .op .output,
                    .op (.regular (.copy 1141 222))]) (.skip)])]) (.skip)]) (.skip)]) (.skip)])]

/-- Source operations of all_cuts. -/
def src_all_cuts : Program :=
  chain [.op (.alloc 1145 64),
  .op (.regular (.copy 260 1145)),
  .op (.alloc 1147 64),
  .op (.regular (.copy 261 1147)),
  .op (.regular (.set 1152 1)),
  .op (.regular (.add 1150 64 1152)),
  .op (.alloc 1149 1150),
  .op (.regular (.copy 262 1149)),
  .op (.regular (.set 1153 0)),
  .op (.regular (.copy 263 1153)),
  .op (.regular (.set 1156 0)),
  .op (.regular (.set 1159 1)),
  .op (.regular (.sub 1157 64 1159)),
  .op (.save 262 1156 1157),
  .op (.regular (.copy 240 259)),
  .op (.regular (.copy 241 260)),
  .op (.regular (.copy 242 261)),
  .op (.regular (.copy 243 263)),
  src_visit,
  .op (.regular (.copy 1160 258)),
  .op (.regular (.set 1165 0)),
  .op (.regular (.copy 264 1165)),
  .cond 6 264 (.op (.regular (.set 1166 0))) (.op (.regular (.set 1166 1))),
  .loop 6 1166 (chain [.op (.fetch 1168 262 263),
      .op (.regular (.copy 265 1168)),
      .op (.regular (.set 1171 0)),
      .op (.regular (.copy 266 1171)),
      .op (.regular (.set 1174 0)),
      .cond 263 1174 (.op (.regular (.set 1172 0))) (.op (.regular (.set 1172 1))),
      .cond 6 1172 (chain [.op (.regular (.set 1180 1)),
          .op (.regular (.sub 1178 263 1180)),
          .op (.fetch 1176 261 1178),
          .op (.regular (.set 1181 1)),
          .op (.regular (.add 1175 1176 1181)),
          .op (.regular (.copy 266 1175))]) (.skip),
      .cond 67 263 (.op (.regular (.set 1183 0))) (.op (.regular (.set 1183 1))),
      .op (.regular (.copy 1182 1183)),
      .cond 6 1182 (chain [.cond 266 265 (.op (.regular (.set 1186 1))) (.op (.regular (.set 1186 0))),
          .op (.regular (.copy 1182 1186))]) (.skip),
      .cond 6 1182 (chain [.op (.regular (.set 1194 1)),
          .op (.regular (.sub 1192 265 1194)),
          .op (.save 262 263 1192),
          .op (.fetch 1195 71 265),
          .cond 6 1195 (chain [.op (.save 261 263 265),
              .op (.regular (.set 1205 1)),
              .op (.save 260 265 1205),
              .op (.regular (.set 1208 1)),
              .op (.regular (.add 1206 263 1208)),
              .op (.regular (.copy 263 1206)),
              .op (.regular (.set 1214 1)),
              .op (.regular (.sub 1212 64 1214)),
              .op (.save 262 263 1212),
              .op (.regular (.copy 240 259)),
              .op (.regular (.copy 241 260)),
              .op (.regular (.copy 242 261)),
              .op (.regular (.copy 243 263)),
              src_visit,
              .op (.regular (.copy 1215 258))]) (.skip)]) (chain [.op (.regular (.set 1222 0)),
          .cond 263 1222 (.cond 1222 263 (.op (.regular (.set 1220 1))) (.op (.regular (.set 1220 0)))) (.op (.regular (.set 1220 0))),
          .cond 6 1220 (chain [.op (.regular (.set 1223 1)),
              .op (.regular (.copy 264 1223))]) (chain [.op (.regular (.set 1226 1)),
              .op (.regular (.sub 1224 263 1226)),
              .op (.regular (.copy 263 1224)),
              .op (.fetch 1229 261 263),
              .op (.regular (.set 1232 0)),
              .op (.save 260 1229 1232)])]),
      .cond 6 264 (.op (.regular (.set 1166 0))) (.op (.regular (.set 1166 1)))])]

/-- Source operations of generate. -/
def src_generate : Program :=
  chain [.op (.regular (.set 1235 1)),
  .op (.regular (.add 1233 66 1235)),
  .op (.regular (.copy 68 1233)),
  .op (.regular (.set 1236 1)),
  .op (.regular (.copy 69 1236)),
  .op (.shift 1237 68 1),
  forCount 268 1239 1237 (chain [.op (.multiply 1240 69 64),
      .op (.regular (.copy 69 1240))]),
  .op (.multiply 1243 68 69),
  .op (.regular (.copy 70 1243)),
  .op (.alloc 1246 64),
  .op (.regular (.copy 71 1246)),
  .op (.alloc 1248 64),
  .op (.regular (.copy 72 1248)),
  .op (.alloc 1250 64),
  .op (.regular (.copy 73 1250)),
  .op (.multiply 1253 64 64),
  .op (.alloc 1252 1253),
  .op (.regular (.copy 74 1252)),
  .op (.multiply 1257 64 64),
  .op (.alloc 1256 1257),
  .op (.regular (.copy 75 1256)),
  .op (.alloc 1260 70),
  .op (.regular (.copy 76 1260)),
  .op (.multiply 1264 64 70),
  .op (.multiply 1263 1264 64),
  .op (.alloc 1262 1263),
  .op (.regular (.copy 77 1262)),
  .op (.multiply 1270 64 70),
  .op (.multiply 1269 1270 64),
  .op (.alloc 1268 1269),
  .op (.regular (.copy 78 1268)),
  .op (.multiply 1276 64 70),
  .op (.multiply 1275 1276 64),
  .op (.alloc 1274 1275),
  .op (.regular (.copy 79 1274)),
  .op (.multiply 1283 64 70),
  .op (.multiply 1282 1283 64),
  .op (.multiply 1281 1282 64),
  .op (.alloc 1280 1281),
  .op (.regular (.copy 80 1280)),
  .op (.multiply 1289 64 70),
  .op (.alloc 1288 1289),
  .op (.regular (.copy 81 1288)),
  .op (.regular (.set 1292 0)),
  .op (.regular (.copy 82 1292)),
  src_build_geometry,
  .op (.regular (.copy 1293 202)),
  forCount 269 1295 64 (chain [.op (.regular (.copy 259 269)),
      src_all_cuts,
      .op (.regular (.copy 1296 267))]),
  .op (.alloc 1298 64),
  .op (.regular (.copy 270 1298)),
  forCount 271 1301 64 (chain [.op (.fetch 1302 71 271),
      .cond 6 1302 (chain [.op (.regular (.copy 132 71)),
          .op (.regular (.copy 133 271)),
          src_component,
          .op (.regular (.copy 1305 138)),
          .op (.regular (.copy 272 1305)),
          .op (.regular (.copy 144 272)),
          src_first,
          .op (.regular (.copy 1309 147)),
          .cond 1309 271 (.cond 271 1309 (.op (.regular (.set 1308 1))) (.op (.regular (.set 1308 0)))) (.op (.regular (.set 1308 0))),
          .cond 6 1308 (chain [.op (.regular (.set 1313 1)),
              .op (.regular (.copy 153 272)),
              .op (.regular (.copy 154 270)),
              .op (.regular (.copy 155 270)),
              src_name_key,
              .op (.regular (.copy 1314 158)),
              .op (.regular (.set 1318 0)),
              .op (.regular (.copy 218 1313)),
              .op (.regular (.copy 219 1314)),
              .op (.regular (.copy 220 1318)),
              .op .output,
              .op (.regular (.copy 1312 222))]) (.skip)]) (.skip)]),
  .op (.regular (.set 1320 4)),
  .op (.regular (.set 1321 0)),
  .op (.regular (.set 1322 0)),
  .op (.regular (.copy 218 1320)),
  .op (.regular (.copy 219 1321)),
  .op (.regular (.copy 220 1322)),
  .op .output,
  .op (.regular (.copy 1319 222)),
  .op (.regular (.set 1325 0)),
  .op (.regular (.set 1326 79)),
  .op (.regular (.sub 1324 1325 1326)),
  .op (.regular (.store 1324 82))]
def candidate (h w:ℕ) := chain [.op (.regular (.set 6 1)),.op (.regular (.set 7 0)),.op (.regular (.set 8 0)),.op (.regular (.copy 64 0)),.op (.regular (.copy 65 3)),.op (.regular (.set 66 (h:ℤ))),.op (.regular (.set 67 (w:ℤ))),src_generate]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical


