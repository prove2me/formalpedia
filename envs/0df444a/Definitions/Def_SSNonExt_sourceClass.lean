-- Prove2me | Definitions.Def_SSNonExt_sourceClass
-- name    : SSNonExt_sourceClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:55.463102+00:00
-- url     : https://prove2.me/theorems/bd70d1f4-e0b8-4151-8a08-21458299b1ae
-- title:
--   The sources $P_T=U_{\Omega_T}$, the class $\mathcal S_b$ and the share support (3)
-- statement:
--   For $T\subseteq V$ let
--
--   $$\Omega_T=\{C_i:i\in T\}\cup\{L_i,R_i:i\notin T\},\qquad Z_T=|\Omega_T|,\qquad P_T=U_{\Omega_T},$$
--
--   the uniform distribution on $\Omega_T$ (which is never empty). The **source class** is $\mathcal S_b=\{P_T:T\subseteq V\}$; it is fixed independently of $\alpha$, the message and any extractor. The set
--
--   $$V\cup\{\bar i:i\notin T\}\subseteq\{0,1\}\times V\tag{3}$$
--
--   consists of all untagged values and the tagged values $\bar i$ with $i\notin T$.
--
--   At every index $i$ a source holds either the central key $C_i$ or the two side keys $L_i,R_i$; this is what makes each single share uniform on (3) and what defeats extraction.
--
--   **Formalization Note** $T^c$ is the complement of the finset $T$ in $V$. Nonemptiness of $\Omega_T$ and of (3) is proved in the module so that the uniform distributions are defined.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §3, display (2), p.6 (PDF p.6); Lemma 3.2, display (3), p.6

import Mathlib
import Definitions.Def_SSNonExt_scheme

namespace SSNonExt

/-- The support `Ω_T = {Cᵢ : i ∈ T} ∪ {Lᵢ, Rᵢ : i ∉ T}` of display (2), p.6.
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §3, display (2), p.6. `Tᶜ` is `V \ T`. -/
noncomputable def Omega {b : ℕ} (T : Finset (V b)) : Finset (Key b) :=
  (T.image fun i => ((Branch.C, i) : Key b)) ∪ (Tᶜ.image fun i => ((Branch.L, i) : Key b)) ∪
    (Tᶜ.image fun i => ((Branch.R, i) : Key b))

/-- `Ω_T` is nonempty: it contains `C₀` if `0 ∈ T` and `L₀` otherwise. -/
theorem Omega_nonempty {b : ℕ} (T : Finset (V b)) : (Omega T).Nonempty := by
  by_cases h : (0 : V b) ∈ T
  · exact ⟨(Branch.C, 0), by simp [Omega, h]⟩
  · exact ⟨(Branch.L, 0), by simp [Omega, h]⟩

/-- The source `P_T = U_{Ω_T}`, uniform on `Ω_T` (display (2), p.6). -/
noncomputable def srcP {b : ℕ} (T : Finset (V b)) : PMF (Key b) :=
  PMF.uniformOfFinset (Omega T) (Omega_nonempty T)

/-- The source class `𝒮_b = {P_T : T ⊆ V}` on the key set `𝒦 = {L, R, C} × V` (§3, p.6). It does
not depend on `α`, on the message, or on any extractor. -/
def srcClass (b : ℕ) : Set (PMF (Key b)) :=
  Set.range (srcP (b := b))

/-- The set `V ∪ {ī : i ∉ T}` of display (3), p.6 (Lemma 3.2): all untagged values and the tagged
values `ī` with `i ∉ T`. -/
noncomputable def shareSupport {b : ℕ} (T : Finset (V b)) : Finset (Share b) :=
  (Finset.univ.image fun x => ((false, x) : Share b)) ∪ (Tᶜ.image fun i => ((true, i) : Share b))

/-- The set (3) is nonempty (it contains the untagged `0`). -/
theorem shareSupport_nonempty {b : ℕ} (T : Finset (V b)) : (shareSupport T).Nonempty :=
  ⟨(false, 0), by simp [shareSupport]⟩

end SSNonExt


