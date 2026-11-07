-- Prove2me | Definitions.Def_ZKSheafPCP_simLaw
-- name    : ZKSheafPCP_simLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:11:34.474525+00:00
-- url     : https://prove2.me/theorems/57f9a33b-f66e-4988-8b3c-f52dff4fb5c3
-- title:
--   The local simulator and the conditional law of the encoding
-- statement:
--   Fix $\sigma$ and $c\in F_\sigma$. The randomized encoding $\mathrm{ENC}_\sigma(c)$ is uniform on $F_{\sigma=c}(P)$. The **local simulator** $\mathrm{Sim}_c(f,Q,\rho)$ outputs $f|_\rho$ if $\rho\in Q$; otherwise, with $A=U_Q$ and $A^*=A\cup P_{\ge\rho}$, it samples $\tilde f$ uniformly from $F_{\sigma=c}(A^*)$ subject to $\tilde f|_{P_A}=f|_{P_A}$, and outputs $\tilde f|_{P_\rho}$.
--
--   The second object here is the conditional probability $\Pr_{\tilde f\leftarrow\mathrm{ENC}_\sigma(c)}[\tilde f|_{P_\rho}=\pi^*\mid\tilde f|_{P_A}=f|_{P_A}]$, written as a ratio of counts.
--
--   **Formalization Note** The uniform law on an empty set defaults to a point mass. Under the hypotheses of Lemma 6.9 the set is nonempty.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Construction 6.8, Definition 6.6, p.26; Lemma 6.9, p.27

import Mathlib
import Definitions.Def_ZKSheafPCP_LocalCodes

namespace ZKSheafPCP

open Classical

/-- The uniform law on a finite set, with an arbitrary default on the empty set. -/
noncomputable def uniformOn {α : Type} (dflt : α) (s : Finset α) : PMF α :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.pure dflt

variable {F D : Type} [Field F] [Fintype F] [Fintype D] (𝓕 : LocalCodes F D) (PP : CodedSpace D)

/-- The law of the output of the local simulator `Sim_c(f, Q, ρ)` (Zeilberger, O'Connor, Gur, Spooner, STOC 2027
submission, manuscript sha256 ac5e528f…, Construction 6.8, p.26). If `ρ ∈ Q`, output `f|_ρ`. Otherwise, with
`A := U_Q` and `A∗ := A ∪ P⩾ρ`, sample `f̃ ← F_{σ=c}(A∗)` uniformly such that `f̃|_{P_A} = f|_{P_A}`, and output
`f̃|_{P_ρ}`. -/
noncomputable def simLaw (σ : Finset D) (c f : D → F) (Q : Finset (Finset D)) (ρ : Finset D) : PMF (D → F) :=
  if ρ ∈ Q then PMF.pure (restr ρ f)
  else (uniformOn 0 (Finset.univ.filter fun g : D → F =>
      g ∈ 𝓕.relSections (PP.geq σ) c (PP.closure Q ∪ PP.geq ρ) ∧
      restr (supp (PP.closure Q)) g = restr (supp (PP.closure Q)) f)).map (restr ρ)

/-- The conditional probability `Pr_{f̃←ENC_σ(c)}[f̃|_{P_ρ} = π∗ | f̃|_{P_A} = f|_{P_A}]`, `A := U_Q` (Lemma 6.9,
p.27), as a ratio of counts: `ENC_σ(c)` is uniform on `F_{σ=c}(P)` (Definition 6.6, p.26). -/
noncomputable def encCond (σ : Finset D) (c f : D → F) (Q : Finset (Finset D)) (ρ : Finset D) (πs : D → F) : ℝ :=
  ((Finset.univ.filter fun g : D → F =>
      g ∈ 𝓕.relSections (PP.geq σ) c PP.P ∧ restr ρ g = πs ∧
      restr (supp (PP.closure Q)) g = restr (supp (PP.closure Q)) f).card : ℝ) /
  ((Finset.univ.filter fun g : D → F =>
      g ∈ 𝓕.relSections (PP.geq σ) c PP.P ∧
      restr (supp (PP.closure Q)) g = restr (supp (PP.closure Q)) f).card : ℝ)

end ZKSheafPCP


