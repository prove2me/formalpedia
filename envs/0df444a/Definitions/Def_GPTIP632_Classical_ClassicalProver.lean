-- Prove2me | Definitions.Def_GPTIP632_Classical_ClassicalProver
-- name    : GPTIP632_Classical_ClassicalProver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:25.899877+00:00
-- url     : https://prove2.me/theorems/ee6df067-b844-4183-b8cb-4ee676b55c38
-- title:
--   Classical randomised provers, the prover's conditional states $\tau_i$, the transcript weights $W$ and $F$, and polynomial-space approximation
-- statement:
--   Fix a verifier $V$ whose messages are classical, an input $x$, and write $q=(q_1,\dots,q_r)$, $a=(a_1,\dots,a_r)$ for the question and answer strings.
--
--   1. For a prover strategy $P$ with channels $\Pi_i$, write $\Pi_i(\delta_q\otimes\tau)=\sum_a\delta_a\otimes\Pi_i^{qa}(\tau)$ (eq. (5)). The prover's **conditional states** are $\tau_0$ and $\tau_i=\Pi_i^{q_ia_i}\circ\cdots\circ\Pi_1^{q_1a_1}(\tau_0)$, and $\pi(a\mid q)=u(\tau_r)$.
--   2. A **classical randomised prover with memory** is a family of conditional distributions $\pi_i(a_i\mid q_1,a_1,\dots,q_{i-1},a_{i-1},q_i)$ on the answer strings of the length of $A_i$. Its acceptance probability is
--   $$\sum_{(z,a)\ \text{accepting}}\Pr_V[z\mid a]\prod_i\pi_i(a_i\mid q_{\le i},a_{<i}).$$
--   A **deterministic prover** $a_i=f_i(q_1,\dots,q_i)$ is the point-mass case.
--   3. The **weight** of a complete transcript is $W(q,a)=\sum_{z\text{ records }q,\ \mathrm{acc}=1}\Pr_V[z\mid a]$, and $F$ is defined on partial transcripts by $F(q,a)=W(q,a)$, $F(h,q)=\max_aF(h,q,a)$ and $F(h)=\sum_qF(h,q)$.
--   4. A real function of encoded inputs is **approximable in polynomial space** within $\varepsilon$ if a deterministic machine halts on every input after visiting polynomially many cells, with a rational within $\varepsilon$ on its work tape. A set of encoded inputs is **decidable in polynomial time** if a clocked machine decides it.
--
--   These objects state Lemmas E.1–E.2 and Facts C.2, E.4.
--
--   **Formalization Note** `jointPre`/`verPre` are the joint and the verifier-only states at the start of each stage; `ProductForm` says the first is the second tensored with a prover vector. Questions and answers are bit strings; histories are lists of question–answer pairs; `Frec k h` is $F$ with $k$ rounds still to play after $h$.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.21 (PDF p.23), Fact C.2; p.25 (PDF p.27), eq. (5), Lemmas E.1–E.2; p.26 (PDF p.28), Fact E.4

import Mathlib
import Definitions.Def_GPTIP632_Classical_Protocol

/-!
# Classical randomised provers, the prover's conditional states, transcript weights, and
# polynomial-space approximation

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), Fact C.2 (p.21, PDF p.23), eq. (5) and
Lemmas E.1–E.2 (p.25, PDF p.27), Fact E.4 (p.26, PDF p.28).

Throughout, `V` is a verifier whose messages are classical registers, so every question and
answer is a bit string recorded when it is exchanged.
-/

noncomputable section

namespace GPTIP632.Classical

open QAlgorithms.Complexity QAdvFew.PoQOracle

attribute [local instance] _root_.Classical.propDecidable

namespace VData

variable {G : Theory} (V : VData G)

/-- The exchanged transcript `(q_1, a_1), …, (q_i, a_i)` of the first `i` rounds. -/
def transcript (q a : ℕ → List Bool) (i : ℕ) : List (List Bool × List Bool) :=
  (List.range i).map fun j => (q j, a j)

/-- The prover's unnormalised conditional state `τ_i(q_1, a_1, …, q_i, a_i) =
Π_i^{q_i a_i} ∘ ⋯ ∘ Π_1^{q_1 a_1}(τ_0)` (Lemma E.1), where `Π^{qa}(τ)` is the `δ_a`-component of
`Π(δ_q ⊗ τ)` (eq. (5), from Fact B.13). -/
def tauVec (x : Str) (P : Prover V x) (q a : ℕ → List Bool) : (i : ℕ) → (G.C.sys (P.P i)).ι → ℝ
  | 0 => P.τ0
  | i + 1 => fun p' =>
    match msgCoord (G := G) (V.A x i) (a i), msgCoord (G := G) (V.Q x i) (q i) with
    | some kA, some kQ => ∑ p, chanKer (P.ch i) kA p' kQ p * tauVec x P q a i p
    | _, _ => 0

/-- `π(a | q) = u(τ_r(q_1, a_1, …, q_r, a_r))`, eq. (6). -/
def proverWeight (x : Str) (P : Prover V x) (q a : ℕ → List Bool) : ℝ :=
  ∑ p, (G.C.sys (P.P (V.R x))).unit p * V.tauVec x P q a (V.R x) p

/-- The joint state (verifier's register and prover's system) at the start of stage `i`, along the
record `(ws, q, a)`, in the interaction with `P`. -/
def jointPre (x : Str) (P : Prover V x) (ws : ℕ → List ℕ) (q a : ℕ → List Bool) (i : ℕ) :=
  V.preStage x (X := fun i => (G.C.sys (P.P i)).ι)
    (fun k p => (if k = [] then 1 else 0) * P.τ0 p) (V.proverExchange x P q a) ws q a i

/-- The verifier's state at the start of stage `i` with the answers `a` fixed on its wires. -/
def verPre (x : Str) (ws : ℕ → List ℕ) (q a : ℕ → List Bool) (i : ℕ) :=
  V.preStage x (X := fun _ => Unit) (fun k _ => if k = [] then 1 else 0)
    (V.fixedExchange x q a) ws q a i

end VData

/-- A joint result is the product `σ ⊗ τ` of a verifier result `σ` and a prover vector `τ`: the same
outcome kind, the same budget and register, and `ψ(k, p) = σ(k) τ(p)` on the register's
coordinates. -/
def ProductForm {G : Theory} {X : Type}
    (r : Res (ℕ × List G.C.Elem × (List G.C.Wire → X → ℝ)))
    (s : Res (ℕ × List G.C.Elem × (List G.C.Wire → Unit → ℝ))) (τ : X → ℝ) : Prop :=
  match r, s with
  | .ok (b, l, ψ), .ok (b', l', σ) => b = b' ∧ l = l' ∧ ∀ k ∈ G.C.coords l, ∀ p, ψ k p = σ k () * τ p
  | .mismatch, .mismatch => True
  | .invalid, .invalid => True
  | _, _ => False

namespace VData

variable {G : Theory} (V : VData G)

/-- A **classical randomised prover with memory** for `V` on `x` (Lemma E.2): conditional
distributions `π_i(a_i | q_1, a_1, …, q_{i-1}, a_{i-1}, q_i)`, given by `resp i h q a` with `h` the
transcript of the earlier rounds; each is a probability distribution on the answer strings of the
length of `A_i`. -/
def IsCRProver (x : Str) (resp : ℕ → List (List Bool × List Bool) → List Bool → List Bool → ℝ) : Prop :=
  (∀ i h q a, 0 ≤ resp i h q a) ∧
  (∀ i h q, ∑ a ∈ strings (V.A x i).length, resp i h q a = 1) ∧
  (∀ i h q a, a.length ≠ (V.A x i).length → resp i h q a = 0)

/-- `∏_i π_i(a_i | q_{≤i}, a_{<i})` over the rounds `i < r(|x|)`. -/
def crWeight (x : Str) (resp : ℕ → List (List Bool × List Bool) → List Bool → List Bool → ℝ)
    (q a : ℕ → List Bool) : ℝ :=
  ∏ i ∈ Finset.range (V.R x), resp i (transcript q a i) (q i) (a i)

/-- The acceptance probability of a classical randomised prover: the total probability
`∑ Pr_V[z | a] ∏_i π_i(a_i | q_{≤i}, a_{<i})` of the accepting records. -/
def crAcc (x : Str) (resp : ℕ → List (List Bool × List Bool) → List Bool → List Bool → ℝ) : ℝ :=
  V.recordSum x fun ws q a => if V.accepts x ws then V.PrV x a ws q * V.crWeight x resp q a else 0

/-- The deterministic prover `a_i = f_i(q_1, …, q_i)` as a classical randomised prover with point
masses (`f i [q_1, …, q_i]`). -/
def detResp (f : ℕ → List (List Bool) → List Bool) :
    ℕ → List (List Bool × List Bool) → List Bool → List Bool → ℝ :=
  fun i h q a => if a = f i (h.map Prod.fst ++ [q]) then 1 else 0

/-- The sum over all gate-outcome records `ws` that can occur on input `x`. -/
def stageSum (x : Str) (F : (ℕ → List ℕ) → ℝ) : ℝ :=
  ∑ f ∈ Fintype.piFinset (fun _ : Fin (V.R x + 1) => natLists (V.B x) (maxOut (G := G))),
    F (extend [] f)

/-- The sum over all records `(ws, q)` (gate outcomes and recorded questions) that can occur. -/
def recordSumWQ (x : Str) (F : (ℕ → List ℕ) → (ℕ → List Bool) → ℝ) : ℝ :=
  ∑ f ∈ Fintype.piFinset (fun _ : Fin (V.R x + 1) => natLists (V.B x) (maxOut (G := G))),
    ∑ fq ∈ Fintype.piFinset (fun _ : Fin (V.R x) => boolLists (V.B x)),
      F (extend [] f) (extend [] fq)

/-- **Fact E.4**: the weight `W(q, a) = ∑_{z records q, acc = 1} Pr_V[z | a]` of a complete
transcript. -/
def W (x : Str) (q a : ℕ → List Bool) : ℝ :=
  V.stageSum x fun ws => if V.accepts x ws then V.PrV x a ws q else 0

/-- The transcript `h` (a list of question–answer pairs) as the question and answer families. -/
def qOf (h : List (List Bool × List Bool)) : ℕ → List Bool := fun j => (h.getD j ([], [])).1

/-- See `qOf`. -/
def aOf (h : List (List Bool × List Bool)) : ℕ → List Bool := fun j => (h.getD j ([], [])).2

theorem strings_nonempty (m : ℕ) : (strings m).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (fun _ : Fin m => false))⟩

/-- **Fact E.4**: the backward recursion over partial transcripts, `k` rounds still to play after the
transcript `h`: `F(q, a) = W(q, a)` at a complete transcript, and
`F(h) = ∑_{q} max_{a} F(h, q, a)` (the next question is summed over, the answer maximised). -/
def Frec (x : Str) : ℕ → List (List Bool × List Bool) → ℝ
  | 0, h => V.W x (qOf h) (aOf h)
  | k + 1, h =>
    ∑ q ∈ strings (V.Q x h.length).length,
      (strings (V.A x h.length).length).sup' (strings_nonempty _) fun a => Frec x k (h ++ [(q, a)])

/-- `F(∅)`. -/
def Fempty (x : Str) : ℝ := V.Frec x (V.R x) []

/-- The encoding of an input and a record: `x`, the stage records, the recorded questions, the
answers (the first `r(|x|) + 1`, `r(|x|)`, `r(|x|)` entries). -/
def encRecord (x : Str) (ws : ℕ → List ℕ) (q a : ℕ → List Bool) : Str :=
  tup [x, tup ((List.range (V.R x + 1)).map fun j => encNats (ws j)),
    tup ((List.range (V.R x)).map q), tup ((List.range (V.R x)).map a)]

end VData

/-- A function `f : α → ℝ` is approximable within `ε` by a **deterministic polynomial-space
algorithm** on the encoded inputs `enc y`: a machine, run with the empty oracle, halts on every input
after visiting at most `s(|enc y|)` cells, with the encoding of a rational within `ε y` of `f y` on its
work tape. -/
def PolySpaceApprox {α : Type} (enc : α → Str) (f ε : α → ℝ) : Prop :=
  ∃ (M : OTM) (s : Polynomial ℕ), ∀ y : α, ∃ T : ℕ, M.result O₀ (enc y) T ≠ none ∧
    M.space O₀ (enc y) T ≤ s.eval (enc y).length ∧
    ∃ r : ℚ, M.output O₀ (enc y) T = encRat r ∧ |(r : ℝ) - f y| ≤ ε y

/-- A predicate on encoded inputs is **decidable in polynomial time**: a clocked deterministic
machine answers it on every input. -/
def PolyTimeDecidable {α : Type} (enc : α → Str) (Z : α → Prop) : Prop :=
  ∃ (M : OTM) (c : Polynomial ℕ), ∀ y : α,
    M.result O₀ (enc y) (c.eval (enc y).length) = some (decide (Z y))

end GPTIP632.Classical

end


