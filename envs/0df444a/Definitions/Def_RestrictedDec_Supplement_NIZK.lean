-- Prove2me | Definitions.Def_RestrictedDec_Supplement_NIZK
-- name    : RestrictedDec_Supplement_NIZK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:28:53.474444+00:00
-- url     : https://prove2.me/theorems/6fd8a1cd-c754-4077-a06a-df7c61d0e4d0
-- title:
--   NIZK proofs: completeness, soundness, one-theorem ZK, simulated acceptance, simulation soundness (Definitions 8–12)
-- statement:
--   A **NIZK proof system** $N=(\mathrm{Setup},\mathrm{Prove},\mathrm{Verify},\mathrm{SimSetup},\mathrm{SimProve})$ for an NP relation $R$ with language $L=\{x:\exists w,\ R(x,w)=1\}$, with explicit coins; efficiency means polynomially many coins and polynomial-time algorithms.
--
--   1. **Perfect completeness** (Def. 8): every honest proof of a true pair verifies under every honest CRS.
--   2. **Computational soundness** (Def. 9): given an honest CRS, no uniform PPT adversary outputs an accepting $(x,\pi)$ with $x\notin L$ except with negligible probability.
--   3. **Adaptive one-theorem zero knowledge** (Def. 10): after seeing the CRS, the adversary returns a true $(x,w)$ and receives either $\mathrm{Prove}(crs,x,w)$ under an honest CRS or $\mathrm{SimProve}(\tau,x)$ under a simulated one; the gap between the two experiments is negligible.
--   4. **Simulated-proof acceptance** (Def. 11): for every uniform PPT selector that sees a simulated CRS and outputs a well-formed statement $x$ (whether or not $x\in L$), $\mathrm{Verify}(crs,x,\mathrm{SimProve}(\tau,x))=1$ except with negligible probability.
--   5. **One-theorem simulation soundness** (Def. 12): after one simulated proof of an adaptively chosen $x^*$, no uniform PPT adversary outputs an accepting $(x,\pi)$ with $x\neq x^*$ and $x\notin L$ except with negligible probability.
--
--   **Formalization Note** In Definitions 10 and 12 an adversary that does not follow the protocol (a false pair, a second query, no query) loses.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.4, pp.33–34, Definitions 8–12

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A **NIZK proof system** `N = (Setup, Prove, Verify, SimSetup, SimProve)`: `setup λ r = crs`;
`prove λ crs x w ρ = π`; `verify λ crs x π ∈ {0, 1}`; `simSetup λ r = (crs, τ)`;
`simProve λ τ x ρ = π`; all randomness explicit.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.4, p.33. -/
structure NIZK where
  crsCoins : ℕ → ℕ
  proveCoins : ℕ → ℕ
  simCoins : ℕ → ℕ
  simProveCoins : ℕ → ℕ
  setup : (lam : ℕ) → (Fin (crsCoins lam) → Bool) → Str
  prove : (lam : ℕ) → Str → Str → Str → (Fin (proveCoins lam) → Bool) → Str
  verify : ℕ → Str → Str → Str → Bool
  simSetup : (lam : ℕ) → (Fin (simCoins lam) → Bool) → Str × Str
  simProve : (lam : ℕ) → Str → Str → (Fin (simProveCoins lam) → Bool) → Str

/-- The proof system is **efficient**: polynomially many coins, and polynomial-time machines,
uniform in `λ`, for `Setup`, for `Prove` under honest reference strings, for `Verify`, for
`SimSetup`, and for `SimProve` under simulated trapdoors. -/
def NIZK.IsEfficient (N : NIZK) : Prop :=
  NoisyOWMPC.PolyBounded N.crsCoins ∧ NoisyOWMPC.PolyBounded N.proveCoins ∧
  NoisyOWMPC.PolyBounded N.simCoins ∧ NoisyOWMPC.PolyBounded N.simProveCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (N.crsCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) = N.setup lam r) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (N.crsCoins lam) → Bool) (x w : Str)
    (ρ : Fin (N.proveCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, N.setup lam r, x, w, List.ofFn ρ]) = N.prove lam (N.setup lam r) x w ρ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (crs x π : Str),
    f (BeyondDS.tup [encNat lam, crs, x, π]) = BeyondDS.encBool (N.verify lam crs x π)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (N.simCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) =
      BeyondDS.tup [(N.simSetup lam r).1, (N.simSetup lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (N.simCoins lam) → Bool) (x : Str)
    (ρ : Fin (N.simProveCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, (N.simSetup lam r).2, x, List.ofFn ρ]) =
      N.simProve lam (N.simSetup lam r).2 x ρ)

/-- **Perfect completeness** for the relation `Rel` (Definition 8): for every `λ`, every honestly
generated `crs` and every `(x, w)` with `R(x, w) = 1`, every proof `π ← Prove(crs, x, w)` verifies.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 8, p.33. -/
def NIZK.Complete (Rel : ℕ → Str → Str → Prop) (N : NIZK) : Prop :=
  ∀ lam (r : Fin (N.crsCoins lam) → Bool) (x w : Str) (ρ : Fin (N.proveCoins lam) → Bool),
    Rel lam x w → N.verify lam (N.setup lam r) x (N.prove lam (N.setup lam r) x w ρ) = true

open Classical in
/-- The success probability in the **computational soundness experiment** (Definition 9):
`crs ← Setup(1^λ)`, the adversary gets `crs` and outputs `tup [x, π]`; it wins iff
`Verify(crs, x, π) = 1` and `x ∉ L = {x : ∃ w, R(x, w)}`. -/
noncomputable def NIZK.soundAdv (Rel : ℕ → Str → Str → Prop) (N : NIZK) (A : Adversary)
    (lam : ℕ) : ℝ :=
  (((PMF.uniformOfFintype (Fin (N.crsCoins lam) → Bool)).bind fun r =>
    interact A lam (σ := Unit) (fun _ o => PMF.pure (.inr (decide
      (N.verify lam (N.setup lam r) (fld o 0) (fld o 1) = true ∧ ¬ ∃ w, Rel lam (fld o 0) w))))
      (A.p.eval lam + 1) () [] (N.setup lam r)) true).toReal

/-- **Computational soundness** (Definition 9): negligible success for every uniform PPT
adversary. Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 9, p.33. -/
def NIZK.Sound (Rel : ℕ → Str → Str → Prop) (N : NIZK) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (N.soundAdv Rel A)

open Classical in
/-- The **challenger of the one-theorem zero-knowledge experiment** `ZK_b` (Definition 10) for a
reference string `crs` and trapdoor `τ` (unused in `ZK₀`). The first move `tup [x, w]` is stage
`A₁`'s output: if `R(x, w) = 1` the adversary receives `π ← Prove(crs, x, w)` (`sim = false`) or
`π ← SimProve(τ, x)` (`sim = true`); otherwise the experiment outputs `0`. The next move is stage
`A₂`'s final bit, the first bit of `fld 0`. -/
noncomputable def NIZK.zkChallenger (Rel : ℕ → Str → Str → Prop) (N : NIZK) (lam : ℕ) (sim : Bool)
    (crs τ : Str) : Bool → Str → PMF ((Bool × Str) ⊕ Bool)
  | false, o =>
    if Rel lam (fld o 0) (fld o 1) then
      if sim then
        (PMF.uniformOfFintype (Fin (N.simProveCoins lam) → Bool)).map fun ρ =>
          .inl (true, N.simProve lam τ (fld o 0) ρ)
      else
        (PMF.uniformOfFintype (Fin (N.proveCoins lam) → Bool)).map fun ρ =>
          .inl (true, N.prove lam crs (fld o 0) (fld o 1) ρ)
    else PMF.pure (.inr false)
  | true, o => PMF.pure (.inr ((fld o 0).headD false))

/-- The gap `|Pr[ZK₀(A, λ) = 1] − Pr[ZK₁(A, λ) = 1]|` (Definition 10): in `ZK₀`, `crs ← Setup(1^λ)`;
in `ZK₁`, `(crs, τ) ← SimSetup(1^λ)`; the adversary first gets `crs`. -/
noncomputable def NIZK.zkGap (Rel : ℕ → Str → Str → Prop) (N : NIZK) (A : Adversary) (lam : ℕ) : ℝ :=
  |(((PMF.uniformOfFintype (Fin (N.crsCoins lam) → Bool)).bind fun r =>
      interact A lam (N.zkChallenger Rel lam false (N.setup lam r) []) (A.p.eval lam + 1)
        false [] (N.setup lam r)) true).toReal -
    (((PMF.uniformOfFintype (Fin (N.simCoins lam) → Bool)).bind fun r =>
      interact A lam (N.zkChallenger Rel lam true (N.simSetup lam r).1 (N.simSetup lam r).2)
        (A.p.eval lam + 1) false [] (N.simSetup lam r).1) true).toReal|

/-- **Adaptive one-theorem zero knowledge** (Definition 10): negligible gap for every uniform PPT
two-stage adversary. Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…),
Definition 10, p.33. -/
def NIZK.ZK (Rel : ℕ → Str → Str → Prop) (N : NIZK) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (N.zkGap Rel A)

open Classical in
/-- The **failure probability of simulated-proof acceptance** (Definition 11) for the instance
space `WF`: `(crs, τ) ← SimSetup(1^λ)`, the selector gets `crs` and outputs `x = fld 0`,
`π ← SimProve(τ, x)`; failure is `x ∈ WF_λ ∧ Verify(crs, x, π) = 0`. -/
noncomputable def NIZK.simRejectProb (WF : ℕ → Str → Prop) (N : NIZK) (D : Adversary) (lam : ℕ) :
    ℝ :=
  (((PMF.uniformOfFintype (Fin (N.simCoins lam) → Bool)).bind fun r =>
    interact D lam (σ := Unit) (fun _ o =>
      (PMF.uniformOfFintype (Fin (N.simProveCoins lam) → Bool)).map fun ρ =>
        .inr (decide (WF lam (fld o 0) ∧ N.verify lam (N.simSetup lam r).1 (fld o 0)
          (N.simProve lam (N.simSetup lam r).2 (fld o 0) ρ) = false)))
      (D.p.eval lam + 1) () [] (N.simSetup lam r).1) true).toReal

/-- **Simulated-proof acceptance** for well-formed statements (Definition 11): for every uniform
PPT statement selector `D`, `Pr[Verify(crs, x, SimProve(τ, x)) = 1] ≥ 1 − negl(λ)` whenever its
output `x` is a syntactically well-formed statement of the public instance space `WF`, whether or
not `x ∈ L`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 11, p.33 ("For every
PPT algorithm D that, after seeing a simulated CRS, outputs an arbitrary syntactically well-formed
polynomial-length statement x from the public instance space (whether or not x ∈ L), …
≥ 1 − negl(λ). We require a uniform negligible bound for PPT statement selectors.").

**Formalization Note.** A selector whose output is not well formed is not penalized; the bound is
stated as negligibility of the failure probability. -/
def NIZK.SimAccept (WF : ℕ → Str → Prop) (N : NIZK) : Prop :=
  ∀ D : Adversary, D.Valid → NoisyOWMPC.Negligible (N.simRejectProb WF D)

open Classical in
/-- The **challenger of the one-theorem simulation-soundness experiment** (Definition 12) under the
simulated `(crs, τ)`; the state is the challenged statement `x*` once chosen. A move `tup [0, x*]`
is the one statement query, answered with `π* ← SimProve(τ, x*)`; a second query ends the
experiment with output `0`. Any other move `tup [·, x, π]` is the output: the adversary wins iff it
made its query, `x ≠ x*`, `Verify(crs, x, π) = 1` and `x ∉ L`. -/
noncomputable def NIZK.ssChallenger (Rel : ℕ → Str → Str → Prop) (N : NIZK) (lam : ℕ)
    (crs τ : Str) : Option Str → Str → PMF ((Option Str × Str) ⊕ Bool)
  | st, o =>
    if fld o 0 = [false] then
      match st with
      | none =>
        (PMF.uniformOfFintype (Fin (N.simProveCoins lam) → Bool)).map fun ρ =>
          .inl (some (fld o 1), N.simProve lam τ (fld o 1) ρ)
      | some _ => PMF.pure (.inr false)
    else PMF.pure (.inr (decide (∃ xs, st = some xs ∧ fld o 1 ≠ xs ∧
      N.verify lam crs (fld o 1) (fld o 2) = true ∧ ¬ ∃ w, Rel lam (fld o 1) w)))

/-- The success probability in the one-theorem simulation-soundness experiment (Definition 12). -/
noncomputable def NIZK.ssAdv (Rel : ℕ → Str → Str → Prop) (N : NIZK) (A : Adversary) (lam : ℕ) :
    ℝ :=
  (((PMF.uniformOfFintype (Fin (N.simCoins lam) → Bool)).bind fun r =>
    interact A lam (N.ssChallenger Rel lam (N.simSetup lam r).1 (N.simSetup lam r).2)
      (A.p.eval lam + 1) none [] (N.simSetup lam r).1) true).toReal

/-- **One-theorem simulation soundness for new statements** (Definition 12): negligible success
for every uniform PPT adversary.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 12, p.34 ("The
adversary adaptively chooses one statement x∗ and receives π∗ = SimProve(τ, x∗). It then outputs
(x, π). The adversary wins iff x ≠ x∗, Verify(crs, x, π) = 1, and x ∉ L."). -/
def NIZK.SimSound (Rel : ℕ → Str → Str → Prop) (N : NIZK) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (N.ssAdv Rel A)

end Supplement

end RestrictedDec


