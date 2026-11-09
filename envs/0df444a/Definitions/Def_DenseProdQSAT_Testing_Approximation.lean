-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_Approximation
-- name    : DenseProdQSAT_Testing_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:17.11755+00:00
-- url     : https://prove2.me/theorems/5a94926d-04aa-4aa0-87d8-9f1b3f3e5c2f
-- title:
--   Support-associated approximate potentials and historical range families
-- statement:
--   For each ordered support $F$, an approximating collection is a length-$L$ sequence of subsets $X_\ell\subseteq V\setminus F$ with $|X_\ell|\le k-1$. Repetitions and the empty set are allowed. The collection is fixed before the assignment states.
--
--   $$\widehat W_A=\frac{e^d n^{k-1}}{L}\sum_{\ell:X_\ell\ne\varnothing}d^{-|X_\ell|}\dim L_A(X_\ell),\qquad\widehat\Delta_A(x,v)=\widehat W_A-\widehat W_{A(x,v)}.$$
--
--   The second potential uses the separate collection associated with $F\cup\{x\}$. The approximate bad set $\widetilde R_i(A)$ quantifies over all prefix times and all compatible unit insertions, with threshold $3\tau_i n^{k-1}/4$. The intermediate family $\mathcal R_{i,F}$ ranges over every local assignment on that fixed ordered support. An accuracy predicate names the absolute error bound $\varepsilon n^{k-1}/256$ for every supported local assignment up to size $4e^d/\tau_J+1$. It is a property proved by Lemma 4.11, not an assumption on quantum instances.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Definitions 4.6–4.7; Eq. (12) p. 16, p. 13

import Definitions.Def_DenseProdQSAT_Testing_Extension
import Definitions.Def_DenseProdQSAT_Testing_FiniteRanges
set_option autoImplicit false

namespace DenseProdQSAT.Testing

/-- Sequences are fixed per support, independently of assigned states. -/
structure ApproximatingCollection (n k L : ℕ) (F : Finset (Fin n)) where
  sets : Fin L → Finset (Fin n)
  outside : ∀ ℓ, sets ℓ ⊆ Finset.univ \ F
  small : ∀ ℓ, (sets ℓ).card ≤ k - 1

noncomputable def ApproxPotential {n k d L : ℕ} (Φ : Instance n k d)
    (F : List (Fin n)) (ψ : States n d)
    (Q : ApproximatingCollection n k L F.toFinset) : ℝ := by
  classical
  exact Real.exp d * (n : ℝ) ^ (k - 1) / L * ∑ ℓ,
    if (Q.sets ℓ).Nonempty then
      ((d : ℝ) ^ (Q.sets ℓ).card)⁻¹ *
        Module.finrank ℂ (ExtensionSpace Φ F.toFinset (Q.sets ℓ) ψ)
    else 0

abbrev CollectionFamily (n k L : ℕ) :=
  (F : List (Fin n)) → ApproximatingCollection n k L F.toFinset

noncomputable def ApproxDrop {n k d L : ℕ} (Φ : Instance n k d)
    (Q : CollectionFamily n k L) (F : List (Fin n)) (ψ : States n d)
    (x : Fin n) (v : Fin d → ℂ) : ℝ :=
  ApproxPotential Φ F ψ (Q F) -
    ApproxPotential Φ (F ++ [x]) (Function.update ψ x v) (Q (F ++ [x]))

noncomputable def ApproxBadSet {n k d L : ℕ} (Φ : Instance n k d)
    (Q : CollectionFamily n k L) (F : List (Fin n)) (ψ : States n d) (i : ℕ) :
    Finset (Fin n) := by
  classical
  exact (Finset.univ \ F.toFinset).filter (fun y => ∀ t ≤ F.length,
    ∀ v : Fin d → ℂ, Compatible Φ (F.take t) ψ y v →
      (3 * Tau i / 4) * (n : ℝ) ^ (k - 1) ≤ ApproxDrop Φ Q (F.take t) ψ y v)

def ApproxRanges {n k d L : ℕ} (Φ : Instance n k d)
    (Q : CollectionFamily n k L) (F : List (Fin n)) (i : ℕ) : Set (Finset (Fin n)) :=
  {R | ∃ ψ : States n d, IsLocal Φ F ψ ∧ R = ApproxBadSet Φ Q F ψ i}

/-- Accuracy of the support-associated sequences, never assumed on an instance. -/
def AccurateFamily {n k d L : ℕ} (Φ : Instance n k d) (ε : ℝ)
    (Q : CollectionFamily n k L) : Prop :=
  ∀ (F : List (Fin n)) (ψ : States n d), IsLocal Φ F ψ →
    (F.length : ℝ) ≤ 4 * Real.exp d / Tau (ScaleCount ε) + 1 →
    |ApproxPotential Φ F ψ (Q F) - Potential Φ F ψ| ≤
      ε / 256 * (n : ℝ) ^ (k - 1)

end DenseProdQSAT.Testing


