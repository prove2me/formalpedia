-- Prove2me | Definitions.Def_InterimRatImpl_Sufficiency_Model
-- name    : InterimRatImpl_Sufficiency_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:42.082987+00:00
-- url     : https://prove2.me/theorems/639f8833-06b0-4980-a4ee-d605e7c85efc
-- title:
--   §§2–6 — interim type spaces, rationalizability, weak IRM and weak NWR
-- statement:
--   A finite type space has agents $I$, nonempty finite type sets $T_i$, beliefs $\pi_i(t_i)$ on the other agents' types, and a finite outcome set $A$. A lottery is a point of $\Delta(A)$, and utilities on lotteries are the expectation of the state-dependent utility of each pure outcome.
--
--   A mechanism has nonempty countable message spaces and a lottery-valued outcome rule. A message survives the operator $b$ for type $t_i$ when it is optimal against a probability belief on the other agents' types and messages whose type marginal is $\pi_i(t_i)$ and whose positive support consists of surviving messages. The rationalizable correspondence $S^\Gamma(T)$ is the largest post-fixed point of $b$.
--
--   Implementation requires a message for every type and the same outcome $\hat f(t)$ at every rationalizable message profile for every state $t$. The file also defines deceptions, weak interim rationalizable monotonicity, strict-if-responsive Bayesian incentive compatibility, and the weak no-worst-rule condition.
--
--   **Formalization Note** Other-agent profiles use dependent functions on indices distinct from $i$. Countable expected payoffs use summable series, and the best-response condition explicitly requires summability.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), pp. 4–18 (PDF 5–19), §§2–6, Definitions 3.1, 4.1–4.4, 5.1, 6.1

import Mathlib

noncomputable section

namespace InterimRatImpl.Sufficiency

universe u v w x

variable {I : Type u} [Fintype I] [DecidableEq I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

abbrev Profile (T : I → Type v) := ∀ i, T i
abbrev Others (T : I → Type v) (i : I) := ∀ j : {j : I // j ≠ i}, T j

def join (i : I) (ti : T i) (s : Others T i) : Profile T :=
  fun j => if h : j = i then h ▸ ti else s ⟨j, h⟩

def others (i : I) (t : Profile T) : Others T i := fun j => t j

abbrev Lottery (A : Type w) [Fintype A] := {p : A → ℝ // p ∈ stdSimplex ℝ A}
abbrev SCF (T : I → Type v) (A : Type w) [Fintype A] := Profile T → Lottery A

/-- The finite interim type space, separated from the outcome and utility data. -/
structure TypeSpace (I : Type u) [Fintype I] [DecidableEq I] (T : I → Type v)
    [∀ i, Fintype (T i)] where
  π : ∀ i, T i → Others T i → ℝ
  π_nonneg : ∀ i ti s, 0 ≤ π i ti s
  π_sum : ∀ i ti, ∑ s, π i ti s = 1

/-- The type space together with the outcome-dependent Bernoulli utility values. -/
structure Env (I : Type u) [Fintype I] [DecidableEq I] (T : I → Type v)
    [∀ i, Fintype (T i)] (A : Type w) where
  typeSpace : TypeSpace I T
  u : I → A → Profile T → ℝ

def eu (E : Env I T A) (i : I) (p : Lottery A) (t : Profile T) : ℝ :=
  ∑ a, p.1 a * E.u i a t

def Support (E : Env I T A) : Set (Profile T) :=
  {t | ∃ i, 0 < E.typeSpace.π i (t i) (others i t)}

def Equiv (Tstar : Set (Profile T)) (f f' : SCF T A) : Prop :=
  ∀ t ∈ Tstar, f t = f' t

def Uy (E : Env I T A) (i : I) (y : Others T i → Lottery A) (ti : T i) : ℝ :=
  ∑ s, E.typeSpace.π i ti s * eu E i (y s) (join i ti s)

def Uf (E : Env I T A) (i : I) (f : SCF T A) (ti : T i) : ℝ :=
  Uy E i (fun s => f (join i ti s)) ti

def Udev (E : Env I T A) (i : I) (f : SCF T A) (t'i ti : T i) : ℝ :=
  Uy E i (fun s => f (join i t'i s)) ti

abbrev MsgCorr (T : I → Type v) (M : I → Type x) :=
  ∀ i, T i → Set (M i)

/-- A correlated belief over other agents' types and messages. The marginal
equation gives total mass one. -/
def IsBeliefFor (E : Env I T A) {M : I → Type x} (i : I) (ti : T i)
    (S : MsgCorr T M) (lam : Others T i × Others M i → ℝ) : Prop :=
  (∀ p, 0 ≤ lam p) ∧
  (∀ p, 0 < lam p → ∀ j : {j : I // j ≠ i}, p.2 j ∈ S j (p.1 j)) ∧
  (∀ s, HasSum (fun m => lam (s, m)) (E.typeSpace.π i ti s))

def payoff (E : Env I T A) {M : I → Type x} (g : Profile M → Lottery A)
    (i : I) (ti : T i) (lam : Others T i × Others M i → ℝ) (mi : M i) : ℝ :=
  ∑' p, lam p * eu E i (g (join i mi p.2)) (join i ti p.1)

def b (E : Env I T A) {M : I → Type x} (g : Profile M → Lottery A)
    (S : MsgCorr T M) : MsgCorr T M :=
  fun i ti => {mi | ∃ lam, IsBeliefFor E i ti S lam ∧
    (∀ mi', Summable (fun p => lam p * eu E i (g (join i mi' p.2)) (join i ti p.1))) ∧
    (∀ mi', payoff E g i ti lam mi' ≤ payoff E g i ti lam mi)}

/-- The largest post-fixed point of the best-response operator. -/
def SGamma (E : Env I T A) {M : I → Type x} (g : Profile M → Lottery A) :
    MsgCorr T M := sSup {S | S ≤ b E g S}

def Implements (E : Env I T A) {M : I → Type x} (Tstar : Set (Profile T))
    (g : Profile M → Lottery A) (f : SCF T A) : Prop :=
  ∃ fhat : SCF T A, Equiv Tstar fhat f ∧
    (∀ i ti, (SGamma E g i ti).Nonempty) ∧
    (∀ t m, (∀ i, m i ∈ SGamma E g i (t i)) → g m = fhat t)

def Implementable (E : Env I T A) (Tstar : Set (Profile T)) (f : SCF T A) : Prop :=
  ∃ (M : I → Type (max u v w)) (_ : ∀ i, Countable (M i)) (_ : ∀ i, Nonempty (M i))
    (g : Profile M → Lottery A), Implements E Tstar g f

structure Deception (T : I → Type v) where
  β : ∀ i, T i → Set (T i)
  self_mem : ∀ i ti, ti ∈ β i ti

def Unacceptable (f : SCF T A) (β : Deception T) : Prop :=
  ∃ t t' : Profile T, (∀ i, t' i ∈ β.β i (t i)) ∧ f t ≠ f t'

def InY (E : Env I T A) (i : I) (ti : T i) (f : SCF T A)
    (y : Others T i → Lottery A) : Prop :=
  (∀ s, y s = f (join i ti s)) ∨ Uy E i y ti < Uf E i f ti

def Sim (f : SCF T A) (i : I) (ti t'i : T i) : Prop :=
  ∀ s, f (join i ti s) = f (join i t'i s)

/-- Definition 4.3. The quantifier over ψ ranges over every compatible
probability distribution, including all possible announced type profiles. -/
def WeaklyRefutable (E : Env I T A) (f : SCF T A) (β : Deception T) : Prop :=
  ∃ i ti t'i, t'i ∈ β.β i ti ∧ ¬ Sim f i t'i ti ∧
    ∀ ψ : {p : Others T i × Profile T → ℝ // p ∈ stdSimplex ℝ (Others T i × Profile T)},
      (∀ s ttilde, 0 < ψ.1 (s, ttilde) →
        ∀ j : {j : I // j ≠ i}, ttilde j ∈ β.β j (s j)) →
      (∀ s, ∑ ttilde, ψ.1 (s, ttilde) = E.typeSpace.π i ti s) →
      ∃ f' : SCF T A,
        (∀ ttilde_i, InY E i ttilde_i f (fun s => f' (join i ttilde_i s))) ∧
        (∑ p, ψ.1 p * eu E i (f (join i t'i (others i p.2))) (join i ti p.1) <
         ∑ p, ψ.1 p * eu E i (f' p.2) (join i ti p.1))

def WeakIRM (E : Env I T A) (f : SCF T A) : Prop :=
  ∀ β : Deception T, Unacceptable f β → WeaklyRefutable E f β

def BIC (E : Env I T A) (f : SCF T A) : Prop :=
  ∀ i ti t'i, Udev E i f t'i ti ≤ Uf E i f ti

def SIRBIC (E : Env I T A) (f : SCF T A) : Prop :=
  BIC E f ∧ ∀ i ti t'i, ¬ Sim f i ti t'i → Udev E i f t'i ti < Uf E i f ti

def InYw (E : Env I T A) (i : I) (ti : T i) (f : SCF T A)
    (y : Others T i → Lottery A) : Prop := Uy E i y ti ≤ Uf E i f ti

def WeakNWR (E : Env I T A) (f : SCF T A) : Prop :=
  ∀ i ti (φ : {p : Others T i × Others T i → ℝ //
      p ∈ stdSimplex ℝ (Others T i × Others T i)}),
    ∃ y y' : Others T i → Lottery A,
      InYw E i ti f y ∧ InYw E i ti f y' ∧
      (∑ p, φ.1 p * eu E i (y p.2) (join i ti p.1) ≠
       ∑ p, φ.1 p * eu E i (y' p.2) (join i ti p.1))

end InterimRatImpl.Sufficiency


