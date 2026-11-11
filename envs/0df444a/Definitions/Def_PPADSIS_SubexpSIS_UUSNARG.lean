-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_UUSNARG
-- name    : PPADSIS_SubexpSIS_UUSNARG
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:48:05.812406+00:00
-- url     : https://prove2.me/theorems/a38ff479-4a1c-4730-8bff-529d563c5fb9
-- title:
--   Unambiguous updatable circuit SNARGs: syntax, completeness, succinctness, (s, δ)-state uniqueness (Definition 4.1)
-- statement:
--   An **unambiguous updatable circuit SNARG (uuSNARG)** for regular tree circuits (§4.1) has a height bound $H=H(\lambda)\ge1$, efficiently computable and polynomially bounded, and algorithms: $\mathrm{Setup}(1^\lambda,1^N)\to\mathrm{crs}$ (probabilistic), and deterministic $\mathrm{Preprocess}(\mathrm{crs},C)\to\mathrm{pp}$, $\mathrm{Initialize}(\mathrm{crs},\mathrm{pp})\to\mathrm{st}_0$, $\mathrm{Update}(\mathrm{crs},\mathrm{pp},\mathrm{st})\to\mathrm{st}'$, $\mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st})\to b$ and $\mathrm{Output}(\mathrm{crs},\mathrm{pp},\mathrm{st})\to y$ or $\bot$. The canonical state is $\mathrm{st}_t:=\mathrm{Update}^t(\mathrm{Initialize}(\mathrm{crs},\mathrm{pp}))$. Supported circuits at $(\lambda,N)$ are regular tree circuits with $p\le H$ and $|C|\le N$.
--
--   - **Completeness:** for all $\lambda,N$, every supported $C$ with output $u_\varepsilon$, every $t\in[0,P]$ and every $\mathrm{crs}$ output by $\mathrm{Setup}(1^\lambda,1^N)$, with $\mathrm{pp}:=\mathrm{Preprocess}(\mathrm{crs},C)$: $\mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st}_t)=1$ and $\mathrm{Output}(\mathrm{st}_P)=u_\varepsilon$.
--   - **Succinctness:** there is a state length $\ell_{\mathrm{st}}(\lambda,N)\le\mathrm{poly}(\lambda,N)$ such that, for supported $C$: Setup runs in time $\mathrm{poly}(\lambda,N)$; Initialize outputs a state of length $\ell_{\mathrm{st}}$ and Update maps states of length $\ell_{\mathrm{st}}$ to states of length $\ell_{\mathrm{st}}$; Preprocess and Initialize run in time $\mathrm{poly}(\lambda,N)$; Update, Verify and Output run in time $\mathrm{poly}(\lambda,N)$ on all inputs whose state has length $\ell_{\mathrm{st}}$.
--   - **$(s,\delta)$-state uniqueness for a size bound $N$** (a polynomial): every adversary $A$ of size $s(\lambda)$ satisfies
--   $$\Pr\left[\begin{array}{l}p\le H\wedge|C|\le N(\lambda)\wedge t\in[0,P]\\ \wedge\ \mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st})=\mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st}')=1\wedge\mathrm{st}\ne\mathrm{st}'\end{array} : \begin{array}{l}\mathrm{crs}\leftarrow\mathrm{Setup}(1^\lambda,1^{N(\lambda)})\\ (C,t,\mathrm{st},\mathrm{st}')\leftarrow A(\mathrm{crs})\\ \mathrm{pp}:=\mathrm{Preprocess}(\mathrm{crs},C)\end{array}\right]\le\delta(\lambda).$$
--     $U$ **has state uniqueness** if for every polynomial $N$ and every polynomial $s$ this holds for some negligible $\delta$.
--
--   The module also defines the probability of Lemma 4.2's event ($A(\mathrm{crs})$ outputs $(C,t,\mathrm{st})$ with $\mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st})=1$ and $\mathrm{st}\ne\mathrm{st}_t$) and the condition that an adversary outputs either $\bot$ or a triple whose time satisfies $t\le\tau$.
--
--   **Formalization Note** `IsUUSNARG` is the syntax with completeness and succinctness; state uniqueness is the separate quantitative property, as Theorems 4.5 and 4.7 assume it separately. Running times are those of one Mathlib `FinTM2` machine per algorithm, required on honest inputs ($\mathrm{crs}$ in Setup's support, supported $C$), with $\mathrm{poly}(\lambda,N)=(\lambda+N+2)^k$; Setup is probabilistic polynomial time on $(1^\lambda,1^N)$. The Lean field for Initialize is `init`. Adversary outputs are codes (`encQuad`, `encTriple`), $\bot$ is the empty output or a failed run, and $C$ must be a well-formed regular tree circuit. Polynomials $N$ are elements of $\mathbb N[X]$.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), pp. 23-24, §4.1 'Height bound', 'Syntax', Definition 4.1; p. 25, Lemma 4.2 (its experiment)

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_PPADSIS_SubexpSIS_Adversary
import Definitions.Def_PPADSIS_SubexpSIS_RegularTreeCircuit

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

open Polynomial

/-- The input `(1^λ, 1^N)` of `Setup`: `1^λ`, a separator `0`, then `1^N`. -/
def setupCode (lN : ℕ × ℕ) : List Bool := unary lN.1 ++ false :: unary lN.2

/-- **Syntax of an unambiguous updatable circuit SNARG** (uuSNARG) for regular tree circuits
(Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission (manuscript sha256 17abad73…), §4.1,
pp. 23–24): a height bound `H` (part of the scheme) and algorithms
- `Setup(1^λ, 1^N) → crs`, probabilistic (explicit coins);
- `Preprocess(crs, C) → pp`, deterministic;
- `Initialize(crs, pp) → st0`, deterministic (the field `init`);
- `Update(crs, pp, st) → st′`, deterministic;
- `Verify(crs, pp, t, st) → b ∈ {0,1}`, deterministic;
- `Output(crs, pp, st) → y` or `⊥` (`none`), deterministic. -/
structure UUSNARG where
  H : ℕ → ℕ
  setup : CoinAlg setupCode
  preprocess : List Bool → RTC → List Bool
  init : List Bool → List Bool → List Bool
  update : List Bool → List Bool → List Bool → List Bool
  verify : List Bool → List Bool → ℕ → List Bool → Bool
  output : List Bool → List Bool → List Bool → Option (List Bool)

namespace UUSNARG

variable (U : UUSNARG)

/-- The **canonical state** `st_t := Update^t(Initialize(crs, pp))` (p. 24). -/
def canon (crs pp : List Bool) (t : ℕ) : List Bool :=
  (U.update crs pp)^[t] (U.init crs pp)

/-- The **height bound** (p. 23): `H` is efficiently computable (from `1^λ` to `1^{H(λ)}` in
polynomial time), polynomially bounded, and `H(λ) ≥ 1`. -/
def HeightOK : Prop :=
  PolyBounded U.H ∧ (∀ lam, 1 ≤ U.H lam) ∧
    PPSLattice.PolyTimeOn unary (fun lam => unary (U.H lam))

/-- The circuits the scheme supports at `(λ, N)`: well-formed regular tree circuits with address
length `p ≤ H(λ)` and size `|C| ≤ N`. -/
def Admissible (lam N : ℕ) (C : RTC) : Prop := C.WF ∧ C.p ≤ U.H lam ∧ C.size ≤ N

/-- **Completeness** (Definition 4.1, p. 24): for all `λ, N`, every supported regular tree circuit
`C` with output `u_ε`, every `t ∈ [0, P]` (`P = 2^p`), and every `crs` that `Setup(1^λ, 1^N)` can
output, with `pp := Preprocess(crs, C)`: `Verify(crs, pp, t, st_t) = 1` and
`Output(st_P) = u_ε` (probability one). -/
def Complete : Prop :=
  ∀ (lam N : ℕ) (C : RTC), U.Admissible lam N C → ∀ t ≤ 2 ^ C.p, ∀ crs,
    U.setup.InSupport (lam, N) crs →
    U.verify crs (U.preprocess crs C) t (U.canon crs (U.preprocess crs C) t) = true ∧
    U.output crs (U.preprocess crs C) (U.canon crs (U.preprocess crs C) (2 ^ C.p)) =
      some C.output

/-- An honest context `(λ, N, C, crs)`: `C` is supported at `(λ, N)` and `crs` is an output of
`Setup(1^λ, 1^N)`. -/
def Honest (a : ℕ × ℕ × RTC × List Bool) : Prop :=
  U.Admissible a.1 a.2.1 a.2.2.1 ∧ U.setup.InSupport (a.1, a.2.1) a.2.2.2

/-- The code of an optional output (`⊥` is `0`, `y` is `1y`). -/
def encOpt : Option (List Bool) → List Bool
  | none => [false]
  | some y => true :: y

/-- **Succinctness** (Definition 4.1, p. 24): there are a state length `ℓ_st(λ, N) ≤ poly(λ, N)`
and one exponent `k` such that, on honest contexts (`p ≤ H`, `|C| ≤ N`, `crs` from `Setup`):
- `Setup` is probabilistic polynomial time on `(1^λ, 1^N)`, so it runs in time `poly(λ, N)`;
- `Initialize` outputs a state of length `ℓ_st`, and `Update` maps every state of length `ℓ_st`
  to a state of length `ℓ_st`;
- `Preprocess` and `Initialize` run in time `(λ + N + 2)^k`;
- `Update`, `Verify` (at times `t ∈ [0, P]`) and `Output` run in time `(λ + N + 2)^k` on all
  inputs whose state has length `ℓ_st`.
Inputs are written with `encPair`; running times are those of one Mathlib `FinTM2` machine per
algorithm. -/
def Succinct : Prop :=
  ∃ (ℓ : ℕ → ℕ → ℕ) (k : ℕ),
    (∀ lam N, ℓ lam N ≤ (lam + N + 2) ^ k) ∧
    U.setup.IsPPT ∧
    (∀ a, U.Honest a →
      (U.init a.2.2.2 (U.preprocess a.2.2.2 a.2.2.1)).length = ℓ a.1 a.2.1 ∧
      ∀ st : List Bool, st.length = ℓ a.1 a.2.1 →
        (U.update a.2.2.2 (U.preprocess a.2.2.2 a.2.2.1) st).length = ℓ a.1 a.2.1) ∧
    TimeBoundedOn (ι := {a : ℕ × ℕ × RTC × List Bool // U.Honest a})
      (fun a => encPair a.1.2.2.2 a.1.2.2.1.enc)
      (fun a => U.preprocess a.1.2.2.2 a.1.2.2.1)
      (fun a => (a.1.1 + a.1.2.1 + 2) ^ k) ∧
    TimeBoundedOn (ι := {a : ℕ × ℕ × RTC × List Bool // U.Honest a})
      (fun a => encPair a.1.2.2.2 (U.preprocess a.1.2.2.2 a.1.2.2.1))
      (fun a => U.init a.1.2.2.2 (U.preprocess a.1.2.2.2 a.1.2.2.1))
      (fun a => (a.1.1 + a.1.2.1 + 2) ^ k) ∧
    TimeBoundedOn
      (ι := {b : (ℕ × ℕ × RTC × List Bool) × List Bool //
        U.Honest b.1 ∧ b.2.length = ℓ b.1.1 b.1.2.1})
      (fun b => encPair b.1.1.2.2.2 (encPair (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1) b.1.2))
      (fun b => U.update b.1.1.2.2.2 (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1) b.1.2)
      (fun b => (b.1.1.1 + b.1.1.2.1 + 2) ^ k) ∧
    TimeBoundedOn
      (ι := {b : (ℕ × ℕ × RTC × List Bool) × ℕ × List Bool //
        U.Honest b.1 ∧ b.2.1 ≤ 2 ^ b.1.2.2.1.p ∧ b.2.2.length = ℓ b.1.1 b.1.2.1})
      (fun b => encPair b.1.1.2.2.2 (encPair (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1)
        (encNat b.1.2.1 ++ b.1.2.2)))
      (fun b => [U.verify b.1.1.2.2.2 (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1) b.1.2.1 b.1.2.2])
      (fun b => (b.1.1.1 + b.1.1.2.1 + 2) ^ k) ∧
    TimeBoundedOn
      (ι := {b : (ℕ × ℕ × RTC × List Bool) × List Bool //
        U.Honest b.1 ∧ b.2.length = ℓ b.1.1 b.1.2.1})
      (fun b => encPair b.1.1.2.2.2 (encPair (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1) b.1.2))
      (fun b => encOpt (U.output b.1.1.2.2.2 (U.preprocess b.1.1.2.2.2 b.1.1.2.2.1) b.1.2))
      (fun b => (b.1.1.1 + b.1.1.2.1 + 2) ^ k)

/-- A **uuSNARG for regular tree circuits** (Definition 4.1, pp. 24): the syntax with an admissible
height bound, completeness and succinctness. State uniqueness is the separate, quantitative
property below (`StateUnique`, `HasStateUniqueness`), as Theorems 4.5 and 4.7 assume it
separately. -/
def IsUUSNARG : Prop := U.HeightOK ∧ U.Complete ∧ U.Succinct

/-- The output `(C, t, st, st′)` of a state-uniqueness adversary, as a string. -/
def encQuad (C : RTC) (t : ℕ) (st st' : List Bool) : List Bool :=
  C.enc ++ encNat t ++ encStr st ++ encStr st'

/-- The advantage of `A` at `λ` in the **state-uniqueness experiment for the size bound `N`**
(Definition 4.1, p. 24): over `crs ← Setup(1^λ, 1^{N(λ)})` and the adversary's coins, the
probability that `A(crs)` outputs `(C, t, st, st′)` with `C` a regular tree circuit,
`p ≤ H ∧ |C| ≤ N(λ) ∧ t ∈ [0, P]`, `Verify(crs, pp, t, st) = Verify(crs, pp, t, st′) = 1` and
`st ≠ st′`, where `pp := Preprocess(crs, C)` (`C` and `t` chosen adaptively). -/
noncomputable def uniqAdv (N : ℕ[X]) (A : Adversary) (lam : ℕ) : ℝ :=
  coinAvg (U.setup.numCoins (lam, N.eval lam)) (fun c =>
    A.prob lam (U.setup.run (lam, N.eval lam) (List.ofFn c)) (fun y =>
      ∃ (C : RTC) (t : ℕ) (st st' : List Bool), y = encQuad C t st st' ∧
        U.Admissible lam (N.eval lam) C ∧ t ≤ 2 ^ C.p ∧
        U.verify (U.setup.run (lam, N.eval lam) (List.ofFn c))
          (U.preprocess (U.setup.run (lam, N.eval lam) (List.ofFn c)) C) t st = true ∧
        U.verify (U.setup.run (lam, N.eval lam) (List.ofFn c))
          (U.preprocess (U.setup.run (lam, N.eval lam) (List.ofFn c)) C) t st' = true ∧
        st ≠ st'))

/-- **`(s, δ)`-state uniqueness for the size bound `N`** (Definition 4.1, p. 24): every adversary
of size `s(λ)` has advantage at most `δ(λ)` in the state-uniqueness experiment, at every `λ`. -/
def StateUnique (s : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ[X]) : Prop :=
  ∀ A : Adversary, A.SizeLE s → ∀ lam, U.uniqAdv N A lam ≤ δ lam

/-- `U` **has state uniqueness** (p. 24): for every polynomial `N` and every polynomial size bound
`s` (here `(λ + 2)^c`), `(s, δ)`-state uniqueness for the size bound `N` holds for some negligible
`δ`. -/
def HasStateUniqueness : Prop :=
  ∀ (N : ℕ[X]) (c : ℕ), ∃ δ : ℕ → ℝ, Negligible δ ∧
    U.StateUnique (fun lam => ((lam : ℝ) + 2) ^ c) δ N

/-- The output `(C, t, st)` of a soundness adversary, as a string. -/
def encTriple (C : RTC) (t : ℕ) (st : List Bool) : List Bool := C.enc ++ encNat t ++ encStr st

/-- The probability in Lemma 4.2 (p. 25): over `crs ← Setup(1^λ, 1^{N(λ)})` and the adversary's
coins, `A(crs)` outputs `(C, t, st)` with `C` a regular tree circuit, `p ≤ H ∧ |C| ≤ N(λ) ∧
t ∈ [0, P]`, `Verify(crs, pp, t, st) = 1` and `st ≠ st_t`, where `pp := Preprocess(crs, C)` and
`st_t := Update^t(Initialize(crs, pp))`. -/
noncomputable def soundAdv (N : ℕ[X]) (A : Adversary) (lam : ℕ) : ℝ :=
  coinAvg (U.setup.numCoins (lam, N.eval lam)) (fun c =>
    A.prob lam (U.setup.run (lam, N.eval lam) (List.ofFn c)) (fun y =>
      ∃ (C : RTC) (t : ℕ) (st : List Bool), y = encTriple C t st ∧
        U.Admissible lam (N.eval lam) C ∧ t ≤ 2 ^ C.p ∧
        U.verify (U.setup.run (lam, N.eval lam) (List.ofFn c))
          (U.preprocess (U.setup.run (lam, N.eval lam) (List.ofFn c)) C) t st = true ∧
        st ≠ U.canon (U.setup.run (lam, N.eval lam) (List.ofFn c))
          (U.preprocess (U.setup.run (lam, N.eval lam) (List.ofFn c)) C) t))

/-- The adversary **outputs either `⊥` or a triple whose time satisfies `t ≤ τ`** (Lemma 4.2,
p. 25): on every `crs` that `Setup(1^λ, 1^{N(λ)})` can output and all coins, a run either fails,
outputs the empty string (`⊥`), or outputs `encTriple C t st` with `t ≤ τ(λ)`. -/
def BotOrTimeBounded (N : ℕ[X]) (τ : ℕ → ℕ) (A : Adversary) : Prop :=
  ∀ (lam : ℕ) (crs : List Bool), U.setup.InSupport (lam, N.eval lam) crs →
    ∀ (c : Fin (A lam crs.length).coins → Bool) (y : List Bool),
      (A lam crs.length).out crs c = some y →
      y = [] ∨ ∃ (C : RTC) (t : ℕ) (st : List Bool), y = encTriple C t st ∧ t ≤ τ lam

end UUSNARG

end PPADSIS.SubexpSIS


