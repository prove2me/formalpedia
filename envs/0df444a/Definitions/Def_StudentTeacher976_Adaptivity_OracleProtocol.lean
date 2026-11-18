-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
-- name    : StudentTeacher976_Adaptivity_OracleProtocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:49:35.277846+00:00
-- url     : https://prove2.me/theorems/0ea140fc-8ea5-432e-a4fe-0262642f84b2
-- title:
--   Bounded oracle computation protocols
-- statement:
--   A pure CPU transforms finite binary words and interacts with one fixed oracle. A response consists of a finality flag, an answer slot, a framed query, and a framed state. On a nonfinal response the driver places the oracle answer into the slot and calls the CPU again; on a final response it asks the CPU to extract the output.
--
--   Write $\operatorname{Trace}(C,O,B;u,v,t)$ when this execution starts with CPU input $u$, finishes with output $v$, makes exactly $t$ oracle calls, and every CPU request and response has length at most $B$:
--
--   $$
--   u \xrightarrow[C,O]{\ t\ \mathrm{queries}\ } v.
--   $$
--
--   This is an inductively defined execution relation. It assumes neither computability of the oracle nor a complexity bound on the CPU. A separate compiler theorem establishes a concrete polynomial-clock oracle machine when the CPU is polynomial-time and polynomial bounds on $t$ and $B$ hold uniformly. The interface supports actual sequential oracle calls in the canonical student and verification algorithms.
-- source:
--   Operational implementation bridge for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7, §3.1 pp.19–20; finite oracle-machine interface and framed binary encodings from the published Cslib/complexitylib development. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

/-- The raw input is distinguished from subsequent CPU requests by an initial 00 prefix. -/
def shifted (x : List Bool) := false::false::x

/-- A CPU response contains its finality flag, an oracle-answer slot, a framed query and
framed state. The marker bit distinguishes responses from initial and final CPU requests. -/
def record (done answer : Bool) (query state : List Bool) : List Bool :=
  true::done::answer::(Turing.MultiTapeTM.frame query ++ Turing.MultiTapeTM.frame state)

/-- A final request asks the CPU to extract the output from its final state. -/
def finalRecord (answer : Bool) (query state : List Bool) :=
  false::true::answer::(Turing.MultiTapeTM.frame query ++ Turing.MultiTapeTM.frame state)

/-- A finite execution of a pure CPU interacting with one oracle. Every response and next
CPU request has encoded size at most B. The natural index counts actual oracle calls;
no computation or complexity hypothesis is built into this relation. -/
inductive Trace (cpu : List Bool → List Bool) (O : QAdvFew.PoQOracle.Oracle) (B : ℕ) :
    List Bool → List Bool → ℕ → Prop
  | done (input : List Bool) (answer : Bool) (q s out : List Bool)
      (hinput : input.length ≤ B) (hsize : (record true answer q s).length ≤ B)
      (hcpu : cpu input = record true answer q s) (hfinal : cpu (finalRecord answer q s) = out) :
      Trace cpu O B input out 0
  | query (input : List Bool) (answer : Bool) (q s out : List Bool) (steps : ℕ)
      (hinput : input.length ≤ B) (hsize : (record false answer q s).length ≤ B)
      (hcpu : cpu input = record false answer q s)
      (next : Trace cpu O B (record false (O q) q s) out steps) :
      Trace cpu O B input out (steps+1)

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver


