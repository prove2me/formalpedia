-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_RSApproximation
-- name    : RandomCNFDeficiency_LowerBound_Supplement_RSApproximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:59.503928+00:00
-- url     : https://prove2.me/theorems/90b9bc52-a344-4f17-aadf-3dd0515e17a7
-- title:
--   Razborov–Smolensky approximators, approximation errors and expected ranks
-- statement:
--   Fix a prime $p$ and positive integers $t_i$ indexed by gate depth. An assignment $A\mapsto \mathrm{App}_A\in\mathbb F_p[x_1,\dots,x_n]$ is a **consistent RS approximation** of a proof if, at every rooted subformula $A$ of every line (Definition A.4): $\mathrm{App}_\bot=0$, $\mathrm{App}_\top=1$, $\mathrm{App}_{x_j}=x_j$, $\mathrm{App}_{\neg A}=1-\mathrm{App}_A$, $\mathrm{App}_{\mathrm{MOD}_{p,b}(A_1,\dots,A_m)}=1-(\sum_j\mathrm{App}_{A_j}-b)^{p-1}$; for a maximal $\vee$-block $A=\bigvee_{j=1}^m A_j$ at depth $i$, $\mathrm{App}_A=1-\prod_j(1-\mathrm{App}_{A_j})$ if $m<t_i$ and otherwise
--
--   $$\mathrm{App}_A=1-\prod_{\nu=1}^{t_i}\bigl(1-q_{A,\nu}^{p-1}\bigr),\qquad q_{A,\nu}=\sum_j\alpha_{j,\nu}\mathrm{App}_{A_j},$$
--
--   for some coefficients $\alpha_{j,\nu}\in\mathbb F_p$; dually $\mathrm{App}_A=\prod_j\mathrm{App}_{A_j}$ or $\prod_\nu(1-r_{A,\nu}^{p-1})$ with $r_{A,\nu}=\sum_j\alpha_{j,\nu}(1-\mathrm{App}_{A_j})$ for $\wedge$-blocks. Identical subformulas share one approximator.
--
--   The **approximation errors** (88) are $e_{A,j}=\mathrm{App}_{A_j}(1-\mathrm{App}_A)$ for $\vee$-blocks and $e_{A,j}=(1-\mathrm{App}_{A_j})\mathrm{App}_A$ for $\wedge$-blocks. The **inference error** of a rule instance $L_1,\dots,L_r\vdash L$ is $E=(\prod_j\mathrm{App}_{L_j})(1-\mathrm{App}_L)$. The degree parameters (49) are $\Delta_0=1$, $\Delta_i=(p-1)t_i\Delta_{i-1}$.
--
--   For $g_1,\dots,g_s$ and coefficients $\alpha\in\mathbb F_p^{t\times s}$ put $q_j=\sum_i\alpha_{j,i}g_i$ and $f_t=\prod_{j=1}^t(1-q_j^{p-1})$. The **expected rank** $\mathbb E[\mathrm{rk}_{f_t,K}]$ is the exact average over all $\alpha$ of the rank of $u\mapsto([f_tg_iu])_i$ on $V_K$ modulo $\mathrm{PC}_D$; the expected kernel dimension averages $\dim(\ker\mathrm{mult}_{f_t,K}/\mathrm{PC}_D(K))$.
--
--   These objects state the kernel-growth estimate (Lemma A.6), the error-derivation lemma (Lemma A.8) and the size–degree relation (Theorem A.3).
--
--   **Formalization Note** $\mathrm{PC}_D$, $V_K$, the multiplication maps, their ranks, $h(K)$, $N_n$, $\eta_K(d)$ and $f_t$ are the published `ResPCDegreeSize.Main` definitions; the random coefficients of Definition A.4 are existential, since Lemma A.8 is asserted for every outcome.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Definition A.4, printed pp. 21–22, PDF pp. 23–24; Equations (47)–(49), (72), (88), printed pp. 20–21, 25, 29, PDF pp. 22–23, 27, 31; Lemma A.6, printed p. 26, PDF p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_ModFrege
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
set_option autoImplicit false
open scoped BigOperators

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound
open ResPCDegreeSize.Main (Poly V CD boolAxioms errorMap cRank hDim eta rsProduct)

/-- The degree parameters of Equation (49): `Δ_0 = 1`, `Δ_i = (p - 1) t_i Δ_{i-1}`. -/
def rsDegree (p : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => (p - 1) * t (i + 1) * rsDegree p t i

/-- Definition A.4 at one rooted syntactic formula `A`: the clause that the approximator `App`
must satisfy at `A`, given the fan-in thresholds `t i` indexed by gate depth `i`.
Constants, variables, negation and `MOD_{p,b}` are exact (Equations (54)–(55)). For the maximal
`∨`-block `A = A₁ ∨ ⋯ ∨ A_m` rooted at `A` (inputs with occurrences, `orInputs`) at depth `i`: if
`m < t i` the evaluation is exact, otherwise `App A = 1 - ∏_ν (1 - q_ν^{p-1})` with
`q_ν = ∑_j α_{j,ν} App A_j` for SOME coefficients `α ∈ F_p` (Equation (56)); dually for `∧`
(Equation (57)). The coefficients are existential here because Lemma A.8 holds for every
outcome of the random choices. -/
def RSLocal {p n : ℕ} (t : ℕ → ℕ) (App : MFormula p (Fin n) → Poly n p) :
    MFormula p (Fin n) → Prop
  | .bot => App .bot = 0
  | .top => App .top = 1
  | .var i => App (.var i) = MvPolynomial.X i
  | .neg A => App (.neg A) = 1 - App A
  | .mod b Γ => App (.mod b Γ) = 1 - ((Γ.map App).sum - MvPolynomial.C b) ^ (p - 1)
  | .or A B =>
      if ((MFormula.or A B).orInputs).length < t (MFormula.or A B).depth then
        App (.or A B) = 1 - (((MFormula.or A B).orInputs).map fun X => 1 - App X).prod
      else
        ∃ α : Fin (t (MFormula.or A B).depth) → Fin ((MFormula.or A B).orInputs).length → ZMod p,
          App (.or A B) = 1 - ∏ ν, (1 - (∑ j, MvPolynomial.C (α ν j) *
            App (((MFormula.or A B).orInputs).get j)) ^ (p - 1))
  | .and A B =>
      if ((MFormula.and A B).andInputs).length < t (MFormula.and A B).depth then
        App (.and A B) = (((MFormula.and A B).andInputs).map App).prod
      else
        ∃ α : Fin (t (MFormula.and A B).depth) → Fin ((MFormula.and A B).andInputs).length → ZMod p,
          App (.and A B) = ∏ ν, (1 - (∑ j, MvPolynomial.C (α ν j) *
            (1 - App (((MFormula.and A B).andInputs).get j))) ^ (p - 1))

/-- Consistent RS approximators for a proof: ONE polynomial `App A` per syntactic formula `A`
(so repeated occurrences share their approximator), satisfying Definition A.4 at every rooted
subformula of every proof line. -/
def IsConsistentRS {p n : ℕ} (t : ℕ → ℕ) (App : MFormula p (Fin n) → Poly n p)
    (π : List (MFormula p (Fin n))) : Prop :=
  ∀ L ∈ π, ∀ A ∈ L.subformulas, RSLocal t App A

/-- The approximation errors `e_{A,j} = g_{A,j} R_A` of Equation (88): for a disjunction block,
`App A_j · (1 - App A)`; for a conjunction block, `(1 - App A_j) · App A`; none otherwise. -/
def approxErrors {p n : ℕ} (App : MFormula p (Fin n) → Poly n p) :
    MFormula p (Fin n) → Set (Poly n p)
  | .or A B => {e | ∃ X ∈ (MFormula.or A B).orInputs, e = App X * (1 - App (.or A B))}
  | .and A B => {e | ∃ X ∈ (MFormula.and A B).andInputs, e = (1 - App X) * App (.and A B)}
  | _ => ∅

/-- All approximation errors `e_{A,j}` of all rooted subformulas `A` of the proof lines. -/
def proofErrors {p n : ℕ} (App : MFormula p (Fin n) → Poly n p)
    (π : List (MFormula p (Fin n))) : Set (Poly n p) :=
  {e | ∃ L ∈ π, ∃ A ∈ L.subformulas, e ∈ approxErrors App A}

/-- The inference error `E = (∏_j App L_j)(1 - App L)` of the rule instance
`σ(F_1), …, σ(F_r) ⊢ σ(F)` (empty product `1` for a zero-premise rule). -/
noncomputable def ruleError {p n : ℕ} (App : MFormula p (Fin n) → Poly n p) (ρ : FregeRule)
    (σ : Fin ρ.m → MFormula p (Fin n)) : Poly n p :=
  (ρ.premises.map fun G => App (G.subst σ)).prod * (1 - App (ρ.conclusion.subst σ))

/-- The random linear combinations `q_j = ∑_i α_{j,i} g_i` of Lemma A.6. -/
noncomputable def rsCombination {p n s t : ℕ} (g : Fin s → Poly n p)
    (α : Fin t → Fin s → ZMod p) (j : Fin t) : Poly n p :=
  ∑ i, MvPolynomial.C (α j i) * g i

/-- `E[rk_{f_t,K}]` in Lemma A.6: the exact uniform average, over all coefficient arrays
`α ∈ F_p^{t × s}`, of the rank of `mult_{f_t,K} : u ↦ ([f_t g_i u])_i` on `V_K`, where
`f_t = ∏_j (1 - q_j^{p-1})` and the published `cRank` is computed modulo `PC_D(Q)`. -/
noncomputable def expectedRank {p n s : ℕ} [NeZero p] (Q : Set (Poly n p)) (D : ℕ)
    (g : Fin s → Poly n p) (t K : ℕ) : ℝ :=
  (∑ α : Fin t → Fin s → ZMod p,
      (cRank Q D g (rsProduct (rsCombination g α)) K : ℝ)) /
    (Fintype.card (Fin t → Fin s → ZMod p) : ℝ)

/-- `dim (ker mult_{f,K} / PC_D(K))`: the kernel of `u ↦ ([f g_i u])_i` on `V_K`, modulo its
intersection with `PC_D`. -/
noncomputable def kernelQuotientDim {p n s : ℕ} (Q : Set (Poly n p)) (D : ℕ)
    (g : Fin s → Poly n p) (f : Poly n p) (K : ℕ) : ℕ :=
  Module.finrank (ZMod p)
    (LinearMap.ker (errorMap Q D g f K) ⧸
      ((CD Q D).comap (V n p K).subtype).comap (LinearMap.ker (errorMap Q D g f K)).subtype)

/-- The expected value of `kernelQuotientDim` for `f = f_t`, uniformly over `α`. -/
noncomputable def expectedKernelQuotientDim {p n s : ℕ} [NeZero p] (Q : Set (Poly n p))
    (D : ℕ) (g : Fin s → Poly n p) (t K : ℕ) : ℝ :=
  (∑ α : Fin t → Fin s → ZMod p,
      (kernelQuotientDim Q D g (rsProduct (rsCombination g α)) K : ℝ)) /
    (Fintype.card (Fin t → Fin s → ZMod p) : ℝ)

end RandomCNFDeficiency.LowerBound.Supplement


