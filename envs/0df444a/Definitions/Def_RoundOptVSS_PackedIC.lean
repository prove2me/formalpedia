-- Prove2me | Definitions.Def_RoundOptVSS_PackedIC
-- name    : RoundOptVSS_PackedIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:41.069276+00:00
-- url     : https://prove2.me/theorems/aeeec828-5203-4f9b-bae3-e71f89bb3707
-- title:
--   Packed information checking: Open, Protocol 3, the IC law, the vote (4) and the keys $K^\pm$
-- statement:
--   Let $\mathbb F$ be a finite field and $\mathbb E$ a field containing it (an $\mathbb F$-algebra). The packed IC of width $h\ge1$ and threshold $t$ uses distinct packing nodes $\beta_1,\dots,\beta_h\in\mathbb F$ (with $\beta_1=0$ when $h=1$), the degree bound $\delta=h+t-1$, the checking-point domain $\mathcal A=\mathbb F\setminus\{0,\beta_1,\dots,\beta_h\}$ and a fixed $\alpha_0\in\mathcal A$. For a polynomial $F\in\mathbb E[X]$ write $\mathrm{val}(F)=(F(\beta_1),\dots,F(\beta_h))$.
--
--   A **valid key** is a triple in $\mathcal A\times\mathbb E\times\mathbb E$; $\mathrm{Norm}(k)=k$ for a valid key and $(\alpha_0,0,0)$ for any other key string. A **valid checkpoint** is $(d,T)$ with $d\in\mathbb F^\times$, $\deg T\le\delta$; a **valid candidate** is $(x',P)$ with $\deg P\le\delta$ and $\mathrm{val}(P)=x'$. Then $\mathrm{Open}(x',P,cp,k)=0$ unless the candidate and $cp=(d,T)$ are valid, in which case, with $(\alpha,y,z)=\mathrm{Norm}(k)$,
--
--   $$\mathrm{Open}(x',P,cp,k)=[P(\alpha)=y]\ \vee\ [T(\alpha)\ne dy+z].$$
--
--   Protocol 3: the sender, on input $x\in\mathbb E^h$, samples uniform $F,G$ of degree at most $\delta$ with $\mathrm{val}(F)=x$, gives $(F,G)$ to the holder and $\mathrm{key}_w=(\alpha_w,F(\alpha_w),G(\alpha_w))$, $\alpha_w\leftarrow\mathcal A$, to each verifier; the holder samples $d\leftarrow\mathbb F^\times$ and broadcasts $cp=(d,dF+G)$; the sender's finish is $\mathsf{ok}$ if $cp$ is valid and $T=dF+G$ as polynomials, and $\mathsf{fail}(x)$ otherwise. The **IC law** of input $x$ is the joint distribution of $(cp,\mathrm{out},(\mathrm{key}_w)_w)$ with honest sender and holder.
--
--   For one label, a **key slot** of party $w$ holds a key or `bad`; its **vote** (4) on a candidate is $\mathrm{Open}$ if the slot holds a valid key and $0$ otherwise. The EARLY value of an active, unreplaced label with candidate $(x',P)$ is $x'$ if at least $t+1$ of the $n$ votes accept and $\bot$ otherwise. For $\alpha\in\mathcal A$ the keys
--
--   $$K^+=(\alpha,P(\alpha),0),\qquad K^-=(\alpha,P(\alpha)+1,\,T(\alpha)-d(P(\alpha)+1))$$
--
--   of Lemma A.5 accept and reject a valid candidate respectively.
--
--   **Formalization Note** Key strings are `Option (𝔼 × 𝔼 × 𝔼)` (`none` = malformed); a key's point is an element of $\mathbb E$, valid when it is the image of a point of $\mathcal A$. The uniform choice of $(F,G)$ is the uniform distribution on coefficient vectors of length $\delta+1$ with $\mathrm{val}(F)=x$.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §5.1 and Protocol 3 (p.17), vote (4) (p.21), Protocol 7 step 1 (p.23), Lemma A.5 proof (p.38)

import Mathlib

open scoped Polynomial ENNReal
open Polynomial Classical

namespace RoundOptVSS

/-!
# Packed information checking (§5.1, Protocol 3) and the EARLY vote (4)

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): §5.1 "A packed realization"
and Protocol 3 (p.17), the vote `Check_L` of (4) (p.21), the EARLY threshold rule of Protocol 7
step 1 (p.23) and the keys `K⁺`, `K⁻` of Lemma A.5 (p.38).

**Formalization Note.**
* `𝔽` is the finite base field (packing nodes, checking points, challenges) and `𝔼` the field
  of payloads, an `𝔽`-algebra; field elements of `𝔽` act on `𝔼` through `algebraMap 𝔽 𝔼`.
* "Degree at most δ" is `natDegree ≤ δ` (the zero polynomial included). `δ = h + t − 1` with the
  standing `h ≥ 1` (§4: "a positive integer h").
* A key (string) is `Option (𝔼 × 𝔼 × 𝔼)`: `none` is a malformed string; a triple is a valid key
  iff its first coordinate is (the image of) a point of `A = 𝔽 \ {0, β₁, …, β_h}` (`K = A × 𝔼 × 𝔼`).
  `Norm` maps every invalid key string to `(α₀, 0, 0)`.
* A checkpoint is a pair `(d, T) ∈ 𝔽 × 𝔼[X]`, valid iff `d ≠ 0` and `deg T ≤ δ`; a candidate is
  `(x′, P) ∈ 𝔼^h × 𝔼[X]`, valid iff `deg P ≤ δ` and `val(P) = x′`.
* The uniform choice of `(F, G)` "of degree at most δ with val(F) = x" is the uniform
  distribution on the coefficient vectors of length `δ + 1` with that constraint (`uniformOn`;
  the set is nonempty under the standing assumptions, and `uniformOn` is then exactly the uniform
  distribution).
-/

/-- The packed-IC parameters: width `h`, threshold `t`, packing nodes `β` and the fixed point
`α₀` used by `Norm`. -/
structure ICParams (𝔽 : Type) where
  h : ℕ
  t : ℕ
  β : Fin h → 𝔽
  α0 : 𝔽

variable {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]

/-- The degree bound `δ = h + t − 1`. -/
def ICParams.δ (I : ICParams 𝔽) : ℕ := I.h + I.t - 1

/-- The checking-point domain `A = 𝔽 \ {0, β₁, …, β_h}`. -/
noncomputable def ICParams.A (I : ICParams 𝔽) : Finset 𝔽 :=
  Finset.univ.filter fun a => a ≠ 0 ∧ ∀ r, a ≠ I.β r

/-- The standing assumptions of §4–§5.1: `h ≥ 1`, distinct packing nodes, `β₁ = 0` when `h = 1`,
and `α₀ ∈ A` (so `A ≠ ∅`). -/
structure ICParams.Standing (I : ICParams 𝔽) : Prop where
  h_pos : 1 ≤ I.h
  β_inj : Function.Injective I.β
  β_zero : I.h = 1 → ∀ r, I.β r = 0
  α0_mem : I.α0 ∈ I.A

/-- A key: three elements of `𝔼`. -/
abbrev ICKey (𝔼 : Type) := 𝔼 × 𝔼 × 𝔼

/-- `val(F) = (F(β₁), …, F(β_h))`. -/
def val (I : ICParams 𝔽) (F : 𝔼[X]) : Fin I.h → 𝔼 :=
  fun r => F.eval (algebraMap 𝔽 𝔼 (I.β r))

/-- A valid key: its point lies in `A`. -/
def KeyValid (I : ICParams 𝔽) (k : ICKey 𝔼) : Prop :=
  ∃ a ∈ I.A, k.1 = algebraMap 𝔽 𝔼 a

/-- `Norm(k) = k` for a valid key and `(α₀, 0, 0)` otherwise (including malformed strings). -/
noncomputable def norm (I : ICParams 𝔽) (k : Option (ICKey 𝔼)) : ICKey 𝔼 :=
  match k with
  | some k0 => if KeyValid I k0 then k0 else (algebraMap 𝔽 𝔼 I.α0, 0, 0)
  | none => (algebraMap 𝔽 𝔼 I.α0, 0, 0)

/-- A valid candidate `(x′, P)`: `deg P ≤ δ` and `val(P) = x′`. -/
def CandValid (I : ICParams 𝔽) (x' : Fin I.h → 𝔼) (P : 𝔼[X]) : Prop :=
  P.natDegree ≤ I.δ ∧ val I P = x'

/-- A valid checkpoint `(d, T)`: `d ∈ 𝔽^×` and `deg T ≤ δ`. -/
def CpValid (I : ICParams 𝔽) (cp : 𝔽 × 𝔼[X]) : Prop :=
  cp.1 ≠ 0 ∧ cp.2.natDegree ≤ I.δ

/-- `Open(x′, P, cp, k) = 1`: the candidate and the checkpoint `cp = (d, T)` are valid and, with
`(α, y, z) = Norm(k)`, `P(α) = y` or `T(α) ≠ d y + z` (p.17). -/
def Accepts (I : ICParams 𝔽) (x' : Fin I.h → 𝔼) (P : 𝔼[X]) (cp : 𝔽 × 𝔼[X])
    (k : Option (ICKey 𝔼)) : Prop :=
  CandValid I x' P ∧ CpValid I cp ∧
    (P.eval (norm I k).1 = (norm I k).2.1 ∨
      cp.2.eval (norm I k).1 ≠ algebraMap 𝔽 𝔼 cp.1 * (norm I k).2.1 + (norm I k).2.2)

/-- The sender's finish in Verify. -/
inductive Finish (𝔼 : Type) (h : ℕ) where
  | ok : Finish 𝔼 h
  | fail : (Fin h → 𝔼) → Finish 𝔼 h

/-- The honest sender's finish: `ok` if `cp = (d, T)` is valid and `T = dF + G` as polynomials,
`fail(x)` otherwise (Protocol 3, Verify round 2). -/
noncomputable def senderFinish (I : ICParams 𝔽) (x : Fin I.h → 𝔼) (F G : 𝔼[X])
    (cp : 𝔽 × 𝔼[X]) : Finish 𝔼 I.h :=
  if CpValid I cp ∧ cp.2 = C (algebraMap 𝔽 𝔼 cp.1) * F + G then .ok else .fail x

/-- The honest holder's checkpoint `cp = (d, dF + G)` (Protocol 3, Verify round 1). -/
noncomputable def holderCheckpoint (d : 𝔽) (F G : 𝔼[X]) : 𝔽 × 𝔼[X] :=
  (d, C (algebraMap 𝔽 𝔼 d) * F + G)

/-- The key `key_w = (α_w, F(α_w), G(α_w))` an honest sender sends to `P_w` (Protocol 3). -/
noncomputable def senderKey (α : 𝔽) (F G : 𝔼[X]) : ICKey 𝔼 :=
  (algebraMap 𝔽 𝔼 α, F.eval (algebraMap 𝔽 𝔼 α), G.eval (algebraMap 𝔽 𝔼 α))

/-- The polynomial with coefficient vector `c`. -/
noncomputable def polyOf {k : ℕ} (c : Fin k → 𝔼) : 𝔼[X] :=
  ∑ i : Fin k, C (c i) * X ^ (i : ℕ)

/-- The uniform distribution on a finite set (a point mass if the set is empty). -/
noncomputable def uniformOn {α : Type} [Fintype α] [Nonempty α] (s : Finset α) : PMF α :=
  if hs : s.Nonempty then PMF.uniformOfFinset s hs else PMF.pure (Classical.arbitrary α)

/-- The sender's polynomial pairs `(F, G)` of degree at most `δ` with `val(F) = x`, as coefficient
vectors. -/
noncomputable def validPairs [Fintype 𝔼] (I : ICParams 𝔽) (x : Fin I.h → 𝔼) :
    Finset ((Fin (I.δ + 1) → 𝔼) × (Fin (I.δ + 1) → 𝔼)) :=
  Finset.univ.filter fun p => val I (polyOf p.1) = x

/-- The law of the public Verify data and the keys with honest sender and honest holder on input
`x` (Distribute and Verify of Protocol 3): `(F, G)` uniform with `val(F) = x`, the challenge
`d ← 𝔽^×`, independent points `α_w ← A` for the `n` verifiers; the result is
`(cp, out, (key_w)_w)` with `cp = (d, dF + G)` and `out` the sender's finish. -/
noncomputable def icLaw [Fintype 𝔼] (I : ICParams 𝔽) (n : ℕ) (x : Fin I.h → 𝔼) :
    PMF ((𝔽 × 𝔼[X]) × Finish 𝔼 I.h × (Fin n → ICKey 𝔼)) :=
  (uniformOn (validPairs I x)).bind fun p =>
    (PMF.uniformOfFintype 𝔽ˣ).bind fun d =>
      (uniformOn (Fintype.piFinset fun _ : Fin n => I.A)).map fun α =>
        let F := polyOf p.1
        let G := polyOf p.2
        let cp := holderCheckpoint (d : 𝔽) F G
        (cp, senderFinish I x F G cp, fun w => senderKey (α w) F G)

/-- The vote (4) of a key slot on a candidate: `Open` if the slot holds a valid key, `0` otherwise
(a `bad` slot is `none`). -/
def Check (I : ICParams 𝔽) (x' : Fin I.h → 𝔼) (P : 𝔼[X]) (cp : 𝔽 × 𝔼[X])
    (k : Option (ICKey 𝔼)) : Prop :=
  (∃ k0, k = some k0 ∧ KeyValid I k0) ∧ Accepts I x' P cp k

/-- The number of accepting votes among all `n` key slots. -/
noncomputable def voteCount (I : ICParams 𝔽) {n : ℕ} (x' : Fin I.h → 𝔼) (P : 𝔼[X])
    (cp : 𝔽 × 𝔼[X]) (k : Fin n → Option (ICKey 𝔼)) : ℕ :=
  (Finset.univ.filter fun w => Check I x' P cp (k w)).card

/-- The EARLY value of an active, unreplaced label with candidate `(x′, P)` and checkpoint `cp`
(Protocol 7, step 1): `x′` iff at least `t + 1` of the `n` votes accept, else ⊥ (`none`). -/
noncomputable def earlyOpen (I : ICParams 𝔽) {n : ℕ} (x' : Fin I.h → 𝔼) (P : 𝔼[X])
    (cp : 𝔽 × 𝔼[X]) (k : Fin n → Option (ICKey 𝔼)) : Option (Fin I.h → 𝔼) :=
  if I.t + 1 ≤ voteCount I x' P cp k then some x' else none

/-- The accepting key `K⁺ = (α, P(α), 0)` of Lemma A.5 (p.38). -/
noncomputable def keyPlus (α : 𝔽) (P : 𝔼[X]) : ICKey 𝔼 :=
  (algebraMap 𝔽 𝔼 α, P.eval (algebraMap 𝔽 𝔼 α), 0)

/-- The rejecting key `K⁻ = (α, P(α) + 1, T(α) − d(P(α) + 1))` of Lemma A.5 (p.38). -/
noncomputable def keyMinus (α : 𝔽) (P : 𝔼[X]) (cp : 𝔽 × 𝔼[X]) : ICKey 𝔼 :=
  (algebraMap 𝔽 𝔼 α, P.eval (algebraMap 𝔽 𝔼 α) + 1,
    cp.2.eval (algebraMap 𝔽 𝔼 α) - algebraMap 𝔽 𝔼 cp.1 * (P.eval (algebraMap 𝔽 𝔼 α) + 1))

end RoundOptVSS


