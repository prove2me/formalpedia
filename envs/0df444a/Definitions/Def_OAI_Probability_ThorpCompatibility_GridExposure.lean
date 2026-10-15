-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
-- name    : OAI_Probability_ThorpCompatibility_GridExposure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:24:27.872143+00:00
-- url     : https://prove2.me/theorems/d96a7726-4fa1-46e2-ad54-de3684cda40c
-- title:
--   Allowed values, output bijections and light-value costs for exposing a column entry
-- statement:
--   Work on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r_i\in S_D$ for $i\in[A]$ and $c_k\in S_A$ for $k\in[D]$. Recall that $a$ is compatible if, for every slot $j\in[D]$, the map $h\mapsto c_{r_h(j)}(h)$ is injective on $[A]$. Let $\star$ denote an unrevealed value, and let $\mathrm{ch}_{k,i}$ and $\mathrm{past}_{e,k,i}$ be the column history and the past of an entry from the exposure order. Fix $k\in[D]$ and $i\in[A]$.
--
--   1. *Past space.* $\mathcal P_{A,D}=\big((S_D)^{[A]}\times(S_A\cup\{\star\})^{[D]}\big)\times([A]\cup\{\star\})^{[A]}$, the set in which $\mathrm{past}_{e,k,i}$ takes its values.
--   2. *Allowed values.* Let $y=((\rho,\pi),v)\in\mathcal P_{A,D}$ and $w\in[A]$, and put $j=\rho_i^{-1}(k)$, the slot that row $i$ sends to column $k$. The value $w$ is allowed for the entry $(k,i)$ at $y$ if
--   $$
--   \forall h\in[A],\ \forall\sigma\in S_A:\qquad \pi_{\rho_h(j)}=\sigma\ \Longrightarrow\ \sigma(h)\ne w .
--   $$
--   In words, $w$ is not already the slot-$j$ output of some row $h$ whose column $\rho_h(j)$ has been revealed. For a compatible $a$, the actual value $c_k(i)$ is always allowed at $\mathrm{past}_{e,k,i}(a)$.
--   3. *Output bijection.* For compatible $a$ and $j\in[D]$, the map $\omega_{a,j}(h)=c_{r_h(j)}(h)$ is a permutation of $[A]$.
--   4. *Column of an output.* For compatible $a$, $j\in[D]$ and $w\in[A]$, set $\kappa_{a,j}(w)=r_h(j)$ with $h=\omega_{a,j}^{-1}(w)$. This is the column through which slot $j$ produces the output $w$. In particular, $\kappa_{a,j}(\omega_{a,j}(h))=r_h(j)$.
--   5. *Column prediction.* For a law $Q$ on the grid and a history value $v$, $\widehat Q_{k,i,v}$ is the conditional law under $Q$ of the entry $c_k(i)$ given $\mathrm{ch}_{k,i}=v$.
--   6. *Light values.* For a threshold $H\in\mathbb{R}$, a value $w\in[A]$ is light for $(k,i,v)$ if $\widehat Q_{k,i,v}(w)\le H/(A-i)$. Here $A-i\ge 1$ is the number of values of $c_k$ not among $c_k(0),\dots,c_k(i-1)$.
--   7. *Column cost.* For $e\in S_D$ and $a\in\mathcal G_{A,D}$, write $v=\mathrm{ch}_{k,i}(a)$, let $\Lambda$ be the set of light values for $(k,i,v)$, and let $\mathcal A$ be the set of values allowed at $\mathrm{past}_{e,k,i}(a)$. Then
--   $$
--   \mathrm{cost}_{e,k,i}(a)=\begin{cases}-\log\dfrac{\widehat Q_{k,i,v}(\Lambda\cap\mathcal A)}{\widehat Q_{k,i,v}(\Lambda)},& c_k(i)\in\Lambda,\\ 0,& c_k(i)\notin\Lambda.\end{cases}
--   $$
--
--   The column cost is nonnegative. When $Q$ is supported on compatible pairs, its $Q$-mean is at most the entropy saved by conditioning on the full past instead of on the column history alone, $H_Q\big(c_k(i)\mid\mathrm{ch}_{k,i}\big)-H_Q\big(c_k(i)\mid\mathrm{past}_{e,k,i}\big)$. For compatible $a$ and $j=r_i^{-1}(k)$, a value $w$ is allowed at $\mathrm{past}_{e,k,i}(a)$ exactly when the column $\kappa_{a,j}(w)$ does not precede $k$, i.e. $e(k)\le e(\kappa_{a,j}(w))$. The average of the cost over a uniformly random order $e$ can therefore be estimated by random-order arguments.
--
--   **Formalization Note** The definitions are `PastSpace`, `gridAllowed`, `outputEquiv` and `columnFor` (both take a proof of `Compatible` as an argument, and the module proves the simp lemmas `outputEquiv_apply` and `columnFor_output`), `columnPrediction`, `columnLight` and `columnCost`. The number $A-i$ is a natural-number subtraction cast to $\mathbb{R}$, and it does not truncate because $i<A$. Lean's conventions $\log 0=0$ and $x/0=0$ make `columnCost` total.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridExposure.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridExposure.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
abbrev PastSpace (A D : ℕ) :=
  (Rows A D × (Fin D → Option (Equiv.Perm (Fin A)))) × (Fin A → Option (Fin A))

noncomputable def gridAllowed {A D : ℕ} (k : Fin D) (i : Fin A)
    (y : PastSpace A D) (w : Fin A) : Prop :=
  ∀ h : Fin A, ∀ σ : Equiv.Perm (Fin A),
    y.1.2 (y.1.1 h ((y.1.1 i).symm k)) = some σ → σ h ≠ w

noncomputable def outputEquiv {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) : Equiv.Perm (Fin A) :=
  Equiv.ofBijective (fun h => a.2 (a.1 h j) h)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨ha j, rfl⟩)

@[simp] lemma outputEquiv_apply {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (h : Fin A) : outputEquiv a ha j h = a.2 (a.1 h j) h := rfl

noncomputable def columnFor {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (w : Fin A) : Fin D := a.1 ((outputEquiv a ha j).symm w) j

@[simp] lemma columnFor_output {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j : Fin D) (h : Fin A) : columnFor a ha j (outputEquiv a ha j h) = a.1 h j := by
  simp only [columnFor, Equiv.symm_apply_apply]

noncomputable def columnPrediction {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (v : Fin A → Option (Fin A)) : Law (Fin A) :=
  Q.predict (fun a => a.2 k i) (colHistory k i) v

noncomputable def columnLight {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (v : Fin A → Option (Fin A)) (w : Fin A) : Prop :=
  (columnPrediction Q k i v).mass w ≤ H / ((A - (i : ℕ) : ℕ) : ℝ)

noncomputable def columnCost {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (a : Grid A D) : ℝ :=
  if columnLight Q H k i (colHistory k i a) (a.2 k i) then
    -Real.log ((columnPrediction Q k i (colHistory k i a)).prob
      (fun w => columnLight Q H k i (colHistory k i a) w ∧
        gridAllowed k i (gridPast e k i a) w) /
          (columnPrediction Q k i (colHistory k i a)).prob (columnLight Q H k i (colHistory k i a)))
  else 0

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI


