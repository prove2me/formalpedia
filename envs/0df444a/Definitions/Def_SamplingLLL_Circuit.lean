-- Prove2me | Definitions.Def_SamplingLLL_Circuit
-- name    : SamplingLLL_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:17.055742+00:00
-- url     : https://prove2.me/theorems/eb256581-b9a5-4a9e-bf78-d00324ec4f5d
-- title:
--   The bidirectional packet circuit: forward and reverse kernels
-- statement:
--   Given a test of the inserted constraint, a packet generator, a sign on labels, entry and exit rows, a router, and the residual partner, the forward kernel repeats: flip a fair coin; on heads, return the configuration if it is good, and otherwise send the residual through the router and exit the resulting packet; on tails, run the generator, retry unchanged on a null or $I^+$ label, and on an $I^-$ label enter its packet, cross the router, exit, and retry. The reverse kernel repeats: one fair-coin branch retries; on the other, run the generator, terminate on a null or $I^-$ label; on an $I^+$ label enter its packet and cross the router; an $I^-$ packet exits and terminates, and a residual output retries.
--
--   These are the procedures whose exactness is Lemma A.6.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.6, proof, p.23

import Mathlib
import Definitions.Def_SamplingLLL_Proc

set_option autoImplicit false

namespace SamplingLLL

open Proc

/-- The ingredients of the bidirectional packet circuit (Appendix A.5, p.23): configuration space
`Ω`, physical labels `T` (`z` of the paper, without the mark) with mark space `M`.
`route t x = none` is the residual label `r`. The router and the residual partner are kernels in `Proc`
on the physical configuration, so any executable coupling (deterministic or randomized) is a circuit. -/
structure Circuit (Ω T M : Type) where
  /-- The test of the inserted constraint (the split (9)); `true` is the good output. -/
  good : Ω → Proc Bool
  /-- The unnormalized packet generator; `none` is the null outcome. -/
  gen : Proc (Option (T × M))
  /-- Whether a label belongs to `I⁻`. -/
  neg : T → Bool
  /-- The entry row `K^in`. -/
  enter : T → M → Ω → Proc Ω
  /-- The exit row `K^out`. -/
  exit : T → Ω → Proc Ω
  /-- The router on physical configurations: from a label and a configuration, the partner label
  (`none` is the residual label). -/
  route : T → Ω → Proc (Option T)
  /-- The router applied to the residual label at a configuration: its partner label. -/
  resid : Ω → Proc T

namespace Circuit

variable {Ω T M : Type} (C : Circuit Ω T M)

/-- Lemma A.6, proof, p.23: the forward kernel from `μ` to `π`. "Flip a fair coin. On heads, run the
residual split, return its good output, and send the residual to the router. On tails, run the
packet generator. A null or `I⁺` label retries unchanged; an `I⁻` label enters its packet and goes
to the router. [...] Every resulting packet exits and retries." -/
noncomputable def forward : Ω → Proc Ω :=
  loop fun x => do
    let h ← flip
    if h then do
      let ok ← C.good x
      if ok then pure (Sum.inr x) else do
        let t ← C.resid x
        let y ← C.exit t x
        pure (Sum.inl y)
    else do
      match ← C.gen with
      | none => pure (Sum.inl x)
      | some (t, k) =>
        if C.neg t then do
          let y ← C.enter t k x
          match ← C.route t y with
          | some t' => do
            let z ← C.exit t' y
            pure (Sum.inl z)
          | none => pure (Sum.inl y)
        else pure (Sum.inl x)

/-- Lemma A.6, proof, p.23: the reverse kernel from `π` to `μ`. "One fair-coin branch retries. On the
other, run the generator. A null or `I⁻` label terminates and returns the current configuration; an
`I⁺` label enters its packet and crosses the router backward. An `I⁻` packet exits and terminates,
while a residual output retries." -/
noncomputable def backward : Ω → Proc Ω :=
  loop fun x => do
    let h ← flip
    if h then pure (Sum.inl x) else do
      match ← C.gen with
      | none => pure (Sum.inr x)
      | some (t, k) =>
        if C.neg t then pure (Sum.inr x) else do
          let y ← C.enter t k x
          match ← C.route t y with
          | none => pure (Sum.inl y)
          | some t' => do
            let z ← C.exit t' y
            pure (Sum.inr z)

end Circuit

end SamplingLLL


