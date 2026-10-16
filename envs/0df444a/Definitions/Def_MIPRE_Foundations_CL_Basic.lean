-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Basic
-- name    : MIPRE_Foundations_CL_Basic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:03:58.474037+00:00
-- url     : https://prove2.me/theorems/c8b380b7-685a-4b4b-bc43-fc2c46fe7fee
-- title:
--   Conditionally linear functions: presentations, evaluation, support, marginals and stage data
-- statement:
--   Let $F$ be a semiring and $\iota$ a type with decidable equality; $F^{\iota}$ is the ambient space, with register subspaces $V_S$ and projections $\mathrm{proj}_S$ (bundle `MIPRE_Foundations_CL_Register`). This bundle formalizes conditionally linear (CL) functions through their *decomposition data* rather than as functions (blueprint `def:cl-function`).
--
--   **Presentations.** `MIPRE.CL.CLFun F ι ℓ` is inductive: `zero : CLFun F ι 0`, and `cons S L₁ next : CLFun F ι (ℓ + 1)` for `S : Finset ι`, `L₁ : RegLinear F S` and a continuation `next : (ι → F) → CLFun F ι ℓ`. `CLFun.eval` is the function presented: $\mathrm{eval}(\mathtt{zero}) = 0$ and
--   $$\mathrm{eval}(\mathtt{cons}\,S\,L_1\,\mathit{next})(x) = L_1 x + \mathrm{eval}\bigl(\mathit{next}(L_1 x)\bigr)\bigl(\mathrm{proj}_{S^{c}}\,x\bigr).$$
--   `CLFun.SupportedOn P T` ("$P$ is on $V_T$"): `zero` always; `cons S L₁ next` when $S \subseteq T$ and every `next v` is on $V_{T \setminus S}$. `CLFun.ExactlyOn P T`: the same with `zero` only for $T = \emptyset$ (the subspaces used along a run partition $T$).
--
--   **Levels.** `CLFun.lift T P` adds a trivial bottom level ($V_T$ with the zero map); `CLFun.liftN T n P` adds $n$ of them. `CLFun.truncate k P` is the $k$-th marginal $L_{\le k}$: `truncate 0 P = zero`, `truncate (k+1) (cons S L₁ next) = cons S L₁ (fun v => truncate k (next v))`, and `truncate (k+1) zero` pads.
--
--   **Stage data.** `CLFun.factorAt P k x : Finset ι` and `CLFun.mapAt P k x` (an endomorphism) are the register subspace and the linear map used at stage $k+1$ on input $x$: $S$ and $L_1$ at `cons S L₁ next` for $k = 0$, recursing into `next (L₁ x)` on $\mathrm{proj}_{S^c} x$ for $k+1$; $\emptyset$ and $0$ beyond the level of $P$. `CLFun.factorOfPrefix P k u` and `CLFun.mapOfPrefix P k u` compute the same from the prefix $u = L_{\le k}(x)$, recursing into `next (proj S u)`.
--
--   The embedded lemmas are the defining equations above as `simp` lemmas, `eq_zero` (every level-$0$ presentation is `zero`), `eval_lift`, `eval_liftN`, `eval_zero_vec`, `eval_truncate_zero`, and `truncate_self`: $P.\mathrm{truncate}\,\ell = P$.
--
--   **Formalization Note**. Two harmless departures from the paper: continuations are indexed by all vectors, and the paper's $V_{>1}$ is $V_{T \setminus S}$ in the one ambient space, not stored. `eval`, `factorAt`, `mapAt` and the prefix versions assume `[Fintype ι]`; the rest only `[Semiring F]` and `[DecidableEq ι]`. `IsCLFun` and the structure lemma `lem:cl-structure` are not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Basic.lean; blueprint def:cl-function, lem:cl-structure; companion paper (vidick/MIPRE-proof), linear.tex, Definition def:cl-func and Lemma lem:cl-kth

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Basic.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register

/-!
# Conditionally linear functions

Blueprint `def:cl-function` (paper `linear.tex`, Definition `def:cl-func`; ledger node
`1.1.2`). The question distribution of every game in the pipeline is *conditionally linear*:
linear maps applied in stages to complementary register subspaces of `V = F^ι`, the register
subspace and the linear map of each stage being allowed to depend on the outputs of the
previous stages.

## Presentations and functions

The paper defines the *set* of `ℓ`-level CL functions on `V` inductively: the `0`-level one is
the zero function, and an `ℓ`-level one is any `L` of the form
`L(x) = L₁(x^{V₁}) + L_{>1, L₁(x^{V₁})}(x^{V_{>1}})` for complementary register subspaces
`V₁ ⊕ V_{>1} = V`, a linear map `L₁` on `V₁`, and `(ℓ-1)`-level CL functions `L_{>1,v}` on
`V_{>1}`, one for each value `v` of `L₁`. Everything downstream — the structure lemma
`lem:cl-kth`, the query interface of a sampler, the hiding tests of introspection — works with
the *decomposition data*, which the function does not determine. So the Lean object is the
data:

* `MIPRE.CL.CLFun F ι ℓ` is the type of `ℓ`-level **presentations** on the ambient space
  `ι → F`. A presentation of level `ℓ + 1` is `cons S L₁ next`: the coordinates `S : Finset ι`
  of the first register subspace `V₁ = V_S`, the first linear map `L₁ : RegLinear F S`, and the
  continuation `next : (ι → F) → CLFun F ι ℓ`, indexed by the value of `L₁`.
* `CLFun.eval` is the function presented:
  `eval (cons S L₁ next) x = L₁ x + eval (next (L₁ x)) (x^{V_{Sᶜ}})`.
* `CLFun.SupportedOn P T` says that `P` is a presentation *on `V_T`* in the paper's sense:
  `S ⊆ T`, and every continuation is on `V_{T \ S}`. The paper's `V_{>1}` is `V_{T \ S}`; it is
  not stored, because the level-`0` presentation `zero` is "the zero function on `V_{T'}`" for
  every `T'` (exactly as in the paper), and this keeps every construction free of
  dependent-type transport.
* `MIPRE.CL.IsCLFun ℓ T f` is the paper's notion itself: some `ℓ`-level presentation on `V_T`
  evaluates to `f`.

Two departures from the letter of the paper, both harmless: continuations are indexed by *all*
vectors rather than by the values of `L₁` (the others are never evaluated), and there is one
ambient space `F^ι` throughout, register subspaces of it playing the role of the paper's
`V_{>1}`, `U ⊕ V`, and so on.

## The structure lemma (`lem:cl-kth`)

`lem:cl-kth` attaches to an `ℓ`-level CL function its marginals `L_{≤k}`, factor spaces
`V_{k,u}` and stage maps `L_{k,u}`, `u` being the prefix `L_{<k}(x)`. Here:

* `CLFun.truncate k P` presents the `k`-th marginal (`P.truncate ℓ = P`, `truncate_self`),
  padded with trivial levels when `k` exceeds the level (`CLFun.lift`, the paper's
  `rk:higher-level`);
* `CLFun.factorAt P k x` and `CLFun.mapAt P k x` are the register subspace and the linear map
  applied at stage `k + 1` on the input `x`. They depend on `x` only through the prefix
  `L_{≤k}(x)`: `CLFun.factorOfPrefix` and `CLFun.mapOfPrefix` compute them from that prefix
  alone (`SupportedOn.factorOfPrefix_eval`, `SupportedOn.mapOfPrefix_eval`), which is what the
  `factor` and `linear` queries of a sampler answer;
* `SupportedOn.eval_truncate_eq_sum` is the decomposition `L_{≤k}(x) = ∑_{i ≤ k} x^{L_i}`, and
  `SupportedOn.disjoint_factorAt`, `SupportedOn.factorAt_subset` say that the factor spaces
  along a run are disjoint register subspaces of `V_T`. `CLFun.ExactlyOn P T` is the
  strengthening under which they partition `T` (`ExactlyOn.biUnion_factorAt`) — item (2) of
  `lem:cl-kth`, which samplers are required to satisfy.
-/

namespace MIPRE.CL

universe u v

/-- Presentations of `ℓ`-level conditionally linear functions on the ambient space `ι → F`
(blueprint `def:cl-function`). `cons S L₁ next` presents `x ↦ L₁ x + next (L₁ x) (x^{V_{Sᶜ}})`. -/
inductive CLFun (F : Type u) [Semiring F] (ι : Type v) [DecidableEq ι] : ℕ → Type (max u v)
  /-- The `0`-level presentation: the zero function. -/
  | zero : CLFun F ι 0
  /-- One more level in front: the register subspace `V_S`, a linear map `L₁` on it, and the
  continuation, chosen according to the value of `L₁`. -/
  | cons {ℓ : ℕ} (S : Finset ι) (L₁ : RegLinear F S) (next : (ι → F) → CLFun F ι ℓ) :
      CLFun F ι (ℓ + 1)

namespace CLFun

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}

theorem eq_zero (P : CLFun F ι 0) : P = zero := by cases P; rfl

/-! ## Support -/
/-- `P.SupportedOn T`: `P` is a presentation on `V_T` — its first register subspace lies inside
`T`, and every continuation is a presentation on the complementary `V_{T \ S}`. -/
def SupportedOn : {ℓ : ℕ} → CLFun F ι ℓ → Finset ι → Prop
  | _, zero, _ => True
  | _, cons S _ next, T => S ⊆ T ∧ ∀ v, (next v).SupportedOn (T \ S)

@[simp] theorem supportedOn_zero (T : Finset ι) : (zero : CLFun F ι 0).SupportedOn T := trivial

@[simp] theorem supportedOn_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (T : Finset ι) :
    (cons S L₁ next).SupportedOn T ↔ S ⊆ T ∧ ∀ v, (next v).SupportedOn (T \ S) := Iff.rfl

/-! ## Levels: padding and marginals -/
/-- One more level at the bottom, acting on the register subspace `V_T` by the zero map: the
paper's `rk:higher-level`, every `ℓ`-level CL function being `(ℓ + 1)`-level. Padding with
`T = ∅` preserves every support; padding with the coordinates not yet used preserves exactness
(`ExactlyOn.lift`). -/
def lift (T : Finset ι) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι (ℓ + 1)
  | _, zero => cons T 0 fun _ => zero
  | _, cons S L₁ next => cons S L₁ fun v => (next v).lift (T \ S)

/-- `n` trivial levels at the bottom. -/
def liftN (T : Finset ι) : (n : ℕ) → CLFun F ι ℓ → CLFun F ι (ℓ + n)
  | 0, P => P
  | n + 1, P => (P.liftN T n).lift T

/-- The first `k` levels of `P`: the `k`-th marginal `L_{≤k}` of `lem:cl-kth`. When `k` exceeds
the level of `P`, the missing levels are trivial. -/
def truncate : (k : ℕ) → {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι k
  | 0, _, _ => zero
  | k + 1, _, zero => (truncate k zero).lift ∅
  | k + 1, _, cons S L₁ next => cons S L₁ fun v => truncate k (next v)

@[simp] theorem truncate_zero (P : CLFun F ι ℓ) : P.truncate 0 = zero := by
  cases P <;> rfl

@[simp] theorem truncate_succ_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) :
    (cons S L₁ next).truncate (k + 1) = cons S L₁ fun v => (next v).truncate k := rfl

theorem truncate_succ_zero (k : ℕ) :
    (zero : CLFun F ι 0).truncate (k + 1) = ((zero : CLFun F ι 0).truncate k).lift ∅ := rfl

/-- Item (4) of `lem:cl-kth`: `L = L_{≤ℓ}`. -/
@[simp] theorem truncate_self (P : CLFun F ι ℓ) : P.truncate ℓ = P := by
  induction P with
  | zero => rfl
  | cons S L₁ next ih =>
    rw [truncate_succ_cons]
    exact congrArg _ (funext ih)

/-! ## Exact support -/

/-- `P.ExactlyOn T`: `P` is a presentation on `V_T` whose last level leaves nothing over, so
that the factor spaces along every run partition `T` (`ExactlyOn.biUnion_factorAt`). This is
item (2) of `lem:cl-kth`, `V = ⊕ᵢ V_{i, L_{<i}(x)}`. -/
def ExactlyOn : {ℓ : ℕ} → CLFun F ι ℓ → Finset ι → Prop
  | _, zero, T => T = ∅
  | _, cons S _ next, T => S ⊆ T ∧ ∀ v, (next v).ExactlyOn (T \ S)

@[simp] theorem exactlyOn_zero (T : Finset ι) : (zero : CLFun F ι 0).ExactlyOn T ↔ T = ∅ :=
  Iff.rfl

@[simp] theorem exactlyOn_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (T : Finset ι) :
    (cons S L₁ next).ExactlyOn T ↔ S ⊆ T ∧ ∀ v, (next v).ExactlyOn (T \ S) := Iff.rfl

/-! ## Evaluation -/

variable [Fintype ι]

/-- The function presented: `L(x) = x^{L₁} + L_{>1, x^{L₁}}(x^{V_{>1}})`. -/
def eval : {ℓ : ℕ} → CLFun F ι ℓ → (ι → F) → (ι → F)
  | _, zero, _ => 0
  | _, cons S L₁ next, x => L₁ x + (next (L₁ x)).eval (proj Sᶜ x)

@[simp] theorem eval_zero (x : ι → F) : (zero : CLFun F ι 0).eval x = 0 := rfl

@[simp] theorem eval_cons {S : Finset ι} (L₁ : RegLinear F S) (next : (ι → F) → CLFun F ι ℓ)
    (x : ι → F) : (cons S L₁ next).eval x = L₁ x + (next (L₁ x)).eval (proj Sᶜ x) := rfl

@[simp] theorem eval_zero_vec (P : CLFun F ι ℓ) : P.eval 0 = 0 := by
  induction P with
  | zero => rfl
  | cons S L₁ next ih => simp [ih]

/-! ## Evaluation of padded and truncated presentations -/

@[simp] theorem eval_lift (T : Finset ι) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.lift T).eval x = P.eval x := by
  induction P generalizing T x with
  | zero => simp [lift]
  | cons S L₁ next ih => simp [lift, ih]

@[simp] theorem eval_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.liftN T n).eval x = P.eval x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liftN, ih]

@[simp] theorem eval_truncate_zero (P : CLFun F ι 0) (k : ℕ) (x : ι → F) :
    (P.truncate k).eval x = 0 := by
  rw [P.eq_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [truncate_succ_zero, eval_lift, ih]

/-! ## The data of a stage -/

/-- The register subspace acted on at stage `k + 1` on the input `x`: the factor space
`V_{k+1,u}` of `lem:cl-kth`, `u = L_{≤k}(x)` the prefix. Beyond the level of `P` it is empty. -/
def factorAt : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, zero, _, _ => ∅
  | _, cons S _ _, 0, _ => S
  | _, cons S L₁ next, k + 1, x => (next (L₁ x)).factorAt k (proj Sᶜ x)

/-- The linear map applied at stage `k + 1` on the input `x`: the map `L_{k+1,u}` of
`lem:cl-kth`, `u = L_{≤k}(x)` the prefix, as an endomorphism of the ambient space. Beyond the
level of `P` it is zero. -/
def mapAt : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → ((ι → F) →ₗ[F] (ι → F))
  | _, zero, _, _ => 0
  | _, cons _ L₁ _, 0, _ => L₁.toLinearMap
  | _, cons S L₁ next, k + 1, x => (next (L₁ x)).mapAt k (proj Sᶜ x)

@[simp] theorem factorAt_zero (k : ℕ) (x : ι → F) : (zero : CLFun F ι 0).factorAt k x = ∅ := rfl

@[simp] theorem factorAt_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (x : ι → F) : (cons S L₁ next).factorAt 0 x = S := rfl

@[simp] theorem factorAt_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (cons S L₁ next).factorAt (k + 1) x = (next (L₁ x)).factorAt k (proj Sᶜ x) := rfl

@[simp] theorem mapAt_zero (k : ℕ) (x : ι → F) : (zero : CLFun F ι 0).mapAt k x = 0 := rfl

@[simp] theorem mapAt_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (x : ι → F) :
    (cons S L₁ next).mapAt 0 x = L₁.toLinearMap := rfl

@[simp] theorem mapAt_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (cons S L₁ next).mapAt (k + 1) x = (next (L₁ x)).mapAt k (proj Sᶜ x) := rfl

/-! ## Stage data from the prefix -/

/-- The factor space at stage `k + 1`, read off the prefix `u = L_{≤k}(x)` rather than the
input `x`: the paper's `V_{k+1,u}`. The prefix determines the branch taken at each earlier
stage — its `V_S`-component is the value of that stage's map — and this is how a sampler's
`factor` query is answered. -/
def factorOfPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, zero, _, _ => ∅
  | _, cons S _ _, 0, _ => S
  | _, cons S _ next, k + 1, u => (next (proj S u)).factorOfPrefix k (proj Sᶜ u)

/-- The linear map at stage `k + 1`, read off the prefix `u = L_{≤k}(x)`: the paper's
`L_{k+1,u}`; how a sampler's `linear` query is answered. -/
def mapOfPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → ((ι → F) →ₗ[F] (ι → F))
  | _, zero, _, _ => 0
  | _, cons _ L₁ _, 0, _ => L₁.toLinearMap
  | _, cons S _ next, k + 1, u => (next (proj S u)).mapOfPrefix k (proj Sᶜ u)

@[simp] theorem factorOfPrefix_zero (k : ℕ) (u : ι → F) :
    (zero : CLFun F ι 0).factorOfPrefix k u = ∅ := rfl

@[simp] theorem factorOfPrefix_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (u : ι → F) : (cons S L₁ next).factorOfPrefix 0 u = S := rfl

@[simp] theorem factorOfPrefix_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (cons S L₁ next).factorOfPrefix (k + 1) u =
      (next (proj S u)).factorOfPrefix k (proj Sᶜ u) := rfl

@[simp] theorem mapOfPrefix_zero (k : ℕ) (u : ι → F) :
    (zero : CLFun F ι 0).mapOfPrefix k u = 0 := rfl

@[simp] theorem mapOfPrefix_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (u : ι → F) :
    (cons S L₁ next).mapOfPrefix 0 u = L₁.toLinearMap := rfl

@[simp] theorem mapOfPrefix_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (cons S L₁ next).mapOfPrefix (k + 1) u =
      (next (proj S u)).mapOfPrefix k (proj Sᶜ u) := rfl

end CLFun

/-! ## The paper's notion -/

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {ℓ : ℕ}

end MIPRE.CL


