-- Prove2me | Definitions.Def_RoundOptVSS_Supplement_KeyUniform
-- name    : RoundOptVSS_Supplement_KeyUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:11:14.871879+00:00
-- url     : https://prove2.me/theorems/7cdba0a6-a9f5-42ab-bc5b-7f476c413f7b
-- title:
--   Statistical WSS (Definition 4.1), broadcast-then-decode schemes (6.1), key-uniform WSS (6.2) and efficient key search (7.7)
-- statement:
--   Fix a protocol with three sharing rounds and one reconstruction round in the execution model of the base mission, with secrets in $\mathbb E^h$. Let $S$ be the honest parties' joint view at the end of sharing. All properties below are required for every valid parameter set ($t<n/2$) satisfying an admissibility predicate (the standing assumptions of a concrete scheme), every corrupt set $C$ with $|C|\le t$ and every static rushing adversary.
--
--   1. **Statistical WSS with error $\varepsilon$ (Definition 4.1).** For every input $x$ and sharing adversary there is a deterministic function $\rho$ of $S$ with values in $\mathbb E^h$, fixed before the reconstruction adversary, such that for every reconstruction adversary: (i) if the dealer is honest, with probability at least $1-\varepsilon$, $\rho(S)=x$ and every honest party outputs $x$; (iii) with probability at least $1-\varepsilon$ all honest parties output the same value $v\in\{\rho(S),\perp\}$. (ii) If the dealer is honest, the adversary's view at the end of sharing has the same law for every two inputs. Correctness and commitment of **Definition 4.2** (with $\rho$ valued in $\mathbb E^h\cup\{\perp\}$ and "all honest parties output $\rho(S)$") and perfect privacy are defined in the same way, and VSS with error $\varepsilon$ is their conjunction.
--   2. **Broadcast-then-decode type with key length $\ell$ (Definition 6.1).** The scheme carries a key length $\ell=\ell(n,t,\kappa)$, independent of $h$; a verification vector $\kappa_j\in\mathbb E^\ell$ and an opening $\omega_j$ computed from party $P_j$'s end-of-sharing state $\sigma_j$, with $\kappa_j$ already determined by its state after sharing round one; a parsing of reconstruction broadcasts into a key vector and an opening (a missing or malformed part is $\mathsf{bad}$); and a public output function $\mathrm{Out}(\sigma_i,K;\tau)$. The property: on every execution, every honest $P_j$'s reconstruction broadcast is delivered and parses to $(\kappa_j,\omega_j)$, and every honest $P_i$ outputs $\mathrm{Out}(\sigma_i,K;\tau)$ for the delivered key vector $K$ and openings $\tau$.
--   3. **Key-uniform WSS with error $\varepsilon$ (Definition 6.2).** A key vector $K$ is *honest-consistent* if $k_j=\kappa_j$ for every honest $j$ (corrupt entries arbitrary in $\mathbb E^\ell\cup\{\mathsf{bad}\}$), and likewise for openings. With $\rho$ the function of Definition 4.1 and $\tau$ the openings actually broadcast, with probability at least $1-\varepsilon$ the following hold **simultaneously for all** honest-consistent $K$: (a) all honest $P_i$ obtain the same $\mathrm{Out}(\sigma_i,K;\tau)\in\{\rho,\perp\}$, equal to $x$ if the dealer is honest with input $x$; (b) for every honest $P_i$ and all honest-consistent $\tau_1,\tau_2$, $\mathrm{Out}(\sigma_i,K;\tau_1)=\perp\iff\mathrm{Out}(\sigma_i,K;\tau_2)=\perp$.
--   4. **Efficient key search (Definition 7.7).** An algorithm $\mathrm{Search}$ that, on a party's state $\sigma_i$, openings $\tau$, a set $Z\subseteq[n]$, keys $c_j\in\mathbb E^\ell\cup\{\mathsf{bad}\}$ for $j\notin Z$ and $b\in\{\mathrm{rej},\mathrm{acc}\}$, returns an assignment $K$ with $k_j=c_j$ for $j\notin Z$ and $\mathrm{Out}(\sigma_i,K;\tau)=\perp$ if $b=\mathrm{rej}$, $\ne\perp$ if $b=\mathrm{acc}$, or returns none exactly when no such assignment exists; exact on every input and not told $C$. Polynomial time of $\mathrm{Out}$ and $\mathrm{Search}$ is stated in the cost model of the supplement (a layout of openings is added).
--
--   These are the notions of Theorems 7.1 and 8.7: Theorem 7.1 asserts them for the scheme of §7.2, and Theorem 8.7 assumes them of a generic scheme.
--
--   **Formalization Note** "With error $\varepsilon$" is quantified over the parameter sets satisfying the predicate `Adm`; with the trivial predicate, VSS is the base mission's `IsVSS`. The output function receives the party's index together with its state. The good event of Definition 6.2 is written as the set of executions on which (a) and (b) hold for every honest-consistent $K$; its outer probability is at least $1-\varepsilon$.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Definitions 4.1 and 4.2 (p.15), Definitions 6.1 and 6.2 (pp.18–19), Definition 7.7 (p.26)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_Recovery
import Definitions.Def_RoundOptVSS_Supplement_Cost

open scoped ENNReal

namespace RoundOptVSS

namespace Supplement

/-!
# Statistical WSS (Definition 4.1), broadcast-then-decode schemes (Definition 6.1), key-uniform
WSS (Definition 6.2) and efficient key search (Definition 7.7)

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): Definitions 4.1 and 4.2 (p.15),
Definitions 6.1 and 6.2 (pp.18–19), Definition 7.7 (p.26).

**Formalization Note.**
* Executions, adversaries, the honest view `S` and Definition 4.2 are the published
  `RoundOptVSS.Model`. A property "with error `ε`" is stated for every valid parameter set
  satisfying an admissibility predicate `Adm` (the standing assumptions of a concrete scheme, such
  as field-size conditions); `IsVSSOn (fun _ => True)` is the published `IsVSS`.
* Definition 4.1: `ρ` takes values in `𝔼^h`, is chosen after the sharing adversary and before
  the reconstruction adversary, correctness uses the same `ρ`, and weak commitment is "all honest
  parties output the same value `v ∈ {ρ(S), ⊥}`".
* Definition 6.1 is a structure `BTD` of data plus the property `IsBTDOn`. The key length is a
  function `keyLen n t κ` of the parameters other than the secret length `h` (and the dealer's
  index, which is a role, not a parameter of the scheme), so "ℓ does not depend on h" holds by
  construction. Verification vectors `vkey` are read from the end-of-sharing state, `vkey1` from
  the state after sharing round one, and on every execution they agree; an opening has an arbitrary
  type `Op`; a received broadcast is parsed into a key vector and an opening (`none` = missing or
  malformed = bad). The output function `Out` receives the party's index together with its state.
* Definition 6.2: one event, of probability at least `1 − ε`, on which (a) and (b) hold for **every**
  honest-consistent key vector `K` at once; `τ` in (a) is the vector of openings actually delivered;
  (b) compares any two honest-consistent opening vectors. `ρ` is the function of Definition 4.1.
* Definition 7.7: `Search` is exact on every input (every state, every opening vector, every free
  set `Z` and fixed keys), is not told `C`, and its search mode is the published `SearchMode`.
  Polynomial time of `Out` and `Search` is measured in the cost model of
  `RoundOptVSS.Supplement.Cost` through a layout of the openings (`BTDLayout`).
-/

variable {Msg St V : Type}

/-- **Definition 4.1** (statistical WSS with error `ε`), for every valid parameter set with
`Adm P`: correctness (i) and weak commitment (iii) with one `ρ : S ↦ 𝔼^h` chosen after the sharing
adversary and before the reconstruction adversary, and perfect privacy (ii). -/
def IsWSSOn (Adm : Params → Prop) (prot : Protocol Msg St V) (ε : Params → ℝ≥0∞) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    (∀ (x : Fin P.h → V) (A : ShareAdv P Msg V),
      ∃ ρ : HonestView P C Msg V → (Fin P.h → V), ∀ B : RecAdv A,
        (P.dealer ∉ C → 1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ρ (Outcome.view (C := C) o) = x ∧ ∀ i, i ∉ C → o.out i = some x}) ∧
        1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ∃ v : Option (Fin P.h → V),
                (v = none ∨ v = some (ρ (Outcome.view (C := C) o))) ∧ ∀ i, i ∉ C → o.out i = v}) ∧
    (P.dealer ∉ C → ∀ (x₀ x₁ : Fin P.h → V) (A : ShareAdv P Msg V),
      (shareExec prot P C x₀ A).map (fun o => o.adv) = (shareExec prot P C x₁ A).map (fun o => o.adv))

/-- Correctness (i) and commitment (iii) of **Definition 4.2** with error `ε`, for every valid
parameter set with `Adm P` (`ρ` valued in `𝔼^h ∪ {⊥}`). -/
def VSSCorrectCommitOn (Adm : Params → Prop) (prot : Protocol Msg St V)
    (ε : Params → ℝ≥0∞) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    ∀ (x : Fin P.h → V) (A : ShareAdv P Msg V),
      ∃ ρ : HonestView P C Msg V → Option (Fin P.h → V), ∀ B : RecAdv A,
        (P.dealer ∉ C → 1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ρ (Outcome.view (C := C) o) = some x ∧ ∀ i, i ∉ C → o.out i = some x}) ∧
        1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ∀ i, i ∉ C → o.out i = ρ (Outcome.view (C := C) o)}

/-- Perfect privacy (ii) of Definitions 4.1 and 4.2, for every valid parameter set with `Adm P`:
with an honest dealer the adversary's view at the end of sharing has the same law for every two
inputs. -/
def PerfectPrivateOn (Adm : Params → Prop) (prot : Protocol Msg St V) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    P.dealer ∉ C → ∀ (x₀ x₁ : Fin P.h → V) (A : ShareAdv P Msg V),
      (shareExec prot P C x₀ A).map (fun o => o.adv) = (shareExec prot P C x₁ A).map (fun o => o.adv)

/-- **Definition 4.2** (statistical VSS with error `ε`) for every valid parameter set with `Adm P`. -/
def IsVSSOn (Adm : Params → Prop) (prot : Protocol Msg St V) (ε : Params → ℝ≥0∞) : Prop :=
  VSSCorrectCommitOn Adm prot ε ∧ PerfectPrivateOn Adm prot

/-- **Definition 6.1** (data): a protocol over `𝔼` with key length `ℓ = keyLen n t κ`, the
verification vector `κ_j` (from the end-of-sharing state `σ_j`, and from the state after sharing
round one), the opening `ω_j`, the parsing of a received reconstruction broadcast into a key vector
and an opening (`none` = missing or malformed = bad), and the output function `Out(σ_i, K; τ)`. -/
structure BTD (𝔼 Msg St Op : Type) where
  prot : Protocol Msg St 𝔼
  keyLen : ℕ → ℕ → ℕ → ℕ
  vkey : (P : Params) → Fin P.n → St → (Fin (keyLen P.n P.t P.κ) → 𝔼)
  vkey1 : (P : Params) → Fin P.n → St → (Fin (keyLen P.n P.t P.κ) → 𝔼)
  opening : (P : Params) → Fin P.n → St → Op
  parseKey : (P : Params) → Msg → Option (Fin (keyLen P.n P.t P.κ) → 𝔼)
  parseOpen : (P : Params) → Msg → Option Op
  Out : (P : Params) → Fin P.n → St → (Fin P.n → Option (Fin (keyLen P.n P.t P.κ) → 𝔼)) →
    (Fin P.n → Option Op) → Option (Fin P.h → 𝔼)

variable {𝔼 Op : Type}

/-- The key length `ℓ` at a parameter set. -/
abbrev BTD.ℓ (S : BTD 𝔼 Msg St Op) (P : Params) : ℕ := S.keyLen P.n P.t P.κ

/-- The key vector `K` delivered in the reconstruction round (missing or malformed = bad). -/
def BTD.deliveredKeys (S : BTD 𝔼 Msg St Op) {P : Params} (bc : Fin P.n → Option Msg) :
    Fin P.n → Option (Fin (S.ℓ P) → 𝔼) :=
  fun j => (bc j).bind (S.parseKey P)

/-- The opening vector `τ` delivered in the reconstruction round. -/
def BTD.deliveredOpenings (S : BTD 𝔼 Msg St Op) {P : Params} (bc : Fin P.n → Option Msg) :
    Fin P.n → Option Op :=
  fun j => (bc j).bind (S.parseOpen P)

/-- **Definition 6.1** (property): on every execution in the support, for all valid parameters
with `Adm P`,
every honest party's reconstruction broadcast is delivered and parses to `(κ_j, ω_j)` computed from
its end-of-sharing state, `κ_j` is already determined by its state after sharing round one, and
every honest party outputs `Out(σ_i, K; τ)` for the delivered `K` and `τ`. -/
def IsBTDOn (Adm : Params → Prop) (S : BTD 𝔼 Msg St Op) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    ∀ (x : Fin P.h → 𝔼) (A : ShareAdv P Msg 𝔼) (B : RecAdv A),
      ∀ o ∈ (exec S.prot P C x A B).support,
        (∀ j, j ∉ C →
          S.deliveredKeys o.recon.bcast j = some (S.vkey P j (o.share.states 3 j)) ∧
          S.deliveredOpenings o.recon.bcast j = some (S.opening P j (o.share.states 3 j)) ∧
          S.vkey P j (o.share.states 3 j) = S.vkey1 P j (o.share.states 1 j)) ∧
        ∀ i, i ∉ C → o.out i =
          S.Out P i (o.share.states 3 i) (S.deliveredKeys o.recon.bcast)
            (S.deliveredOpenings o.recon.bcast)

/-- `K` is honest-consistent: `k_j = κ_j` for every honest `j` (corrupt entries arbitrary). -/
def HonestConsistentKey (S : BTD 𝔼 Msg St Op) (P : Params) (C : Finset (Fin P.n))
    (σ : Fin P.n → St) (K : Fin P.n → Option (Fin (S.ℓ P) → 𝔼)) : Prop :=
  ∀ j, j ∉ C → K j = some (S.vkey P j (σ j))

/-- `τ` is honest-consistent: `w_j = ω_j` for every honest `j` (corrupt entries arbitrary). -/
def HonestConsistentOpen (S : BTD 𝔼 Msg St Op) (P : Params) (C : Finset (Fin P.n))
    (σ : Fin P.n → St) (τ : Fin P.n → Option Op) : Prop :=
  ∀ j, j ∉ C → τ j = some (S.opening P j (σ j))

/-- The event of **Definition 6.2** for one instance with end-of-sharing states `σ`, committed value
`ρ`, dealer input `x` (used only when the dealer is honest) and actual openings `τ`: for every
honest-consistent `K`, (a) all honest parties obtain the same `Out(σ_i, K; τ) ∈ {ρ, ⊥}`, equal to
`x` if the dealer is honest, and (b) for every honest `P_i` and all honest-consistent `τ₁, τ₂`,
`Out(σ_i, K; τ₁) = ⊥ ⇔ Out(σ_i, K; τ₂) = ⊥`. -/
def KUEvent (S : BTD 𝔼 Msg St Op) (P : Params) (C : Finset (Fin P.n)) (σ : Fin P.n → St)
    (ρ x : Fin P.h → 𝔼) (τ : Fin P.n → Option Op) : Prop :=
  ∀ K : Fin P.n → Option (Fin (S.ℓ P) → 𝔼), HonestConsistentKey S P C σ K →
    (∃ v : Option (Fin P.h → 𝔼), (v = none ∨ v = some ρ) ∧
      (∀ i, i ∉ C → S.Out P i (σ i) K τ = v) ∧ (P.dealer ∉ C → v = some x)) ∧
    ∀ i, i ∉ C → ∀ τ₁ τ₂ : Fin P.n → Option Op,
      HonestConsistentOpen S P C σ τ₁ → HonestConsistentOpen S P C σ τ₂ →
        (S.Out P i (σ i) K τ₁ = none ↔ S.Out P i (σ i) K τ₂ = none)

/-- A **key-uniform WSS with error `ε`** (Definitions 4.1 and 6.2), for every valid parameter set
with `Adm P`: one `ρ` (chosen after the sharing adversary, before the reconstruction adversary)
witnesses correctness and weak commitment of Definition 4.1 and, with probability at least
`1 − ε`, the event of Definition 6.2 with the actual openings; and the sharing phase is perfectly
private. -/
def IsKeyUniformWSSOn (Adm : Params → Prop) (S : BTD 𝔼 Msg St Op) (ε : Params → ℝ≥0∞) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    (∀ (x : Fin P.h → 𝔼) (A : ShareAdv P Msg 𝔼),
      ∃ ρ : HonestView P C Msg 𝔼 → (Fin P.h → 𝔼), ∀ B : RecAdv A,
        (P.dealer ∉ C → 1 - ε P ≤ (exec S.prot P C x A B).toOuterMeasure
            {o | ρ (Outcome.view (C := C) o) = x ∧ ∀ i, i ∉ C → o.out i = some x}) ∧
        1 - ε P ≤ (exec S.prot P C x A B).toOuterMeasure
            {o | ∃ v : Option (Fin P.h → 𝔼),
                (v = none ∨ v = some (ρ (Outcome.view (C := C) o))) ∧ ∀ i, i ∉ C → o.out i = v} ∧
        1 - ε P ≤ (exec S.prot P C x A B).toOuterMeasure
            {o | KUEvent S P C (o.share.states 3) (ρ (Outcome.view (C := C) o)) x
                (S.deliveredOpenings o.recon.bcast)}) ∧
    (P.dealer ∉ C → ∀ (x₀ x₁ : Fin P.h → 𝔼) (A : ShareAdv P Msg 𝔼),
      (shareExec S.prot P C x₀ A).map (fun o => o.adv) =
        (shareExec S.prot P C x₁ A).map (fun o => o.adv))

/-- The type of a key-search algorithm (Definition 7.7): party index and state, openings `τ`, free
set `Z`, keys `c` (entries in `Z` ignored) and mode `b ∈ {rej, acc}`. -/
abbrev SearchFn (S : BTD 𝔼 Msg St Op) : Type :=
  (P : Params) → Fin P.n → St → (Fin P.n → Option Op) → Finset (Fin P.n) →
    (Fin P.n → Option (Fin (S.ℓ P) → 𝔼)) → SearchMode →
      Option (Fin P.n → Option (Fin (S.ℓ P) → 𝔼))

/-- An assignment `K` meets a search request: `k_j = c_j` for `j ∉ Z`, and `Out(σ_i, K; τ) = ⊥`
exactly when the mode is `rej`. -/
def MeetsRequest (S : BTD 𝔼 Msg St Op) (P : Params) (i : Fin P.n) (σ : St)
    (τ : Fin P.n → Option Op) (Z : Finset (Fin P.n)) (c K : Fin P.n → Option (Fin (S.ℓ P) → 𝔼))
    (b : SearchMode) : Prop :=
  (∀ j, j ∉ Z → K j = c j) ∧
    match b with
    | .rej => S.Out P i σ K τ = none
    | .acc => S.Out P i σ K τ ≠ none

/-- **Definition 7.7** (exactness): for all valid parameters with `Adm P` and on every input,
`Search` returns an assignment meeting the request,
or `none` iff no assignment meets it. -/
def IsExactSearchOn (Adm : Params → Prop) (S : BTD 𝔼 Msg St Op) (Search : SearchFn S) : Prop :=
  ∀ (P : Params), P.Valid → Adm P → ∀ (i : Fin P.n) (σ : St) (τ : Fin P.n → Option Op) (Z : Finset (Fin P.n))
    (c : Fin P.n → Option (Fin (S.ℓ P) → 𝔼)) (b : SearchMode),
    (∀ K, Search P i σ τ Z c b = some K → MeetsRequest S P i σ τ Z c K b) ∧
    (Search P i σ τ Z c b = none ↔ ¬ ∃ K, MeetsRequest S P i σ τ Z c K b)

/-- A layout of a broadcast-then-decode scheme: a protocol layout plus a layout of openings. -/
structure BTDLayout (𝔼 Msg St Op : Type) extends Layout 𝔼 Msg St where
  op : Op → MVal 𝔼

/-- The search mode as a bit (`rej ↦ 1`). -/
def modeBit : SearchMode → Bool
  | .rej => true
  | .acc => false

/-- Input of `Out`: parameters, party, state, key vector, openings. -/
def outIn (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op) (P : Params) (i : Fin P.n) (σ : St)
    (K : Fin P.n → Option (Fin (S.ℓ P) → 𝔼)) (τ : Fin P.n → Option Op) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), L.st σ, layFin (layOpt layVec) K, layFin (layOpt L.op) τ]

/-- Input of `Search`: parameters, party, state, openings, the indicator of `Z`, keys, mode. -/
def searchIn (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op) (P : Params) (i : Fin P.n)
    (σ : St) (τ : Fin P.n → Option Op) (Z : Finset (Fin P.n))
    (c : Fin P.n → Option (Fin (S.ℓ P) → 𝔼)) (b : SearchMode) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), L.st σ, layFin (layOpt L.op) τ,
    layFin (fun j : Fin P.n => layBool (decide (j ∈ Z))) id, layFin (layOpt layVec) c,
    layBool (modeBit b)]

variable (𝔽 : Type) [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]

/-- `Out` is computed by the program `code` within `p(N(P) + input size)` steps on every
input, for all valid parameters with `Adm P` (Definition 6.1, "public deterministic polynomial-time"). -/
def OutComputed (Adm : Params → Prop) (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op)
    (N : Params → ℕ) (p : Polynomial ℕ) (code : Program) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ i σ K τ,
    RunsWithin 𝔽 code (outIn S L P i σ K τ) (layOpt layVec (S.Out P i σ K τ))
      (p.eval (N P + valSize (outIn S L P i σ K τ)))

/-- `Search` is computed by the program `code` within `p(N(P) + input size)` steps on
every input, for all valid parameters with `Adm P` (Definition 7.7, "deterministic polynomial-time"). -/
def SearchComputed (Adm : Params → Prop) (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op)
    (Search : SearchFn S) (N : Params → ℕ) (p : Polynomial ℕ) (code : Program) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ i σ τ Z c b,
    RunsWithin 𝔽 code (searchIn S L P i σ τ Z c b)
      (layOpt (layFin (layOpt layVec)) (Search P i σ τ Z c b))
      (p.eval (N P + valSize (searchIn S L P i σ τ Z c b)))

end Supplement

end RoundOptVSS


