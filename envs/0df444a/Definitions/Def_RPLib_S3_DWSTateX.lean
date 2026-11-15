-- Prove2me | Definitions.Def_RPLib_S3_DWSTateX
-- name    : RPLib_S3_DWSTateX
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:57:54.62174+00:00
-- url     : https://prove2.me/theorems/d2252fe5-044c-4a4e-b18d-d7928544a8ca
-- title:
--   Weight-two Ramanujan-Petersson library: prime-to-`p` isogeny data from the Tate pullbacks
-- statement:
--   Prime-to-`p` isogeny data from the Tate pullbacks.
--
--   From `f : K(E') → K(E)`, `g : K(E) → K(E')` with `(f ∘ g)(x, y) = N • (x, y)` and `p ∤ N`:
--   the Vélu quotient `q : E → E/H` (`H` from `HT`), the isomorphism `σ : L(E') ≃ L(E/H)` (`exists_velu_sigma`),
--   `θ : E/H → E'` with inverse `θ'` (`exists_conj`, `conj_inv`), the Vélu dual `ψ_H`, and
--   **`exists_isog_data`** : `u := θ ∘ q`, `w := ψ_H ∘ θ'` are isogenies with `w ∘ u = [n]`, `u ∘ w = [n]`, `p ∤ n`, and
--   `u` commutes with Frobenius (the hypotheses of `exists_quotClass_of_isog`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateW
import Definitions.Def_RPLib_S3_DWSTateS

/-!
# S3-DWS-Tate, part X: prime-to-`p` isogeny data from the Tate pullbacks

From `f : K(E') → K(E)`, `g : K(E) → K(E')` with `(f ∘ g)(x, y) = N • (x, y)` and `p ∤ N`:
the Vélu quotient `q : E → E/H` (`H` from `HT`), the isomorphism `σ : L(E') ≃ L(E/H)` (`exists_velu_sigma`),
`θ : E/H → E'` with inverse `θ'` (`exists_conj`, `conj_inv`), the Vélu dual `ψ_H`, and
**`exists_isog_data`** : `u := θ ∘ q`, `w := ψ_H ∘ θ'` are isogenies with `w ∘ u = [n]`, `u ∘ w = [n]`, `p ∤ n`, and
`u` commutes with Frobenius (the hypotheses of `exists_quotClass_of_isog`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Data

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L] {N : ℕ}

attribute [local instance] finite_coordinateRing decEqFF

/-- **Prime-to-`p` isogeny data from the Tate pullbacks.** -/
theorem exists_isog_data [Algebra.IsAlgebraic F L] (hNF : (N : F) ≠ 0)
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) [Fintype (HT L N f)] :
    ∃ n : ℕ, (n : F) ≠ 0 ∧ ∃ u : Pt W L →+ Pt W' L, ∃ w : Pt W' L →+ Pt W L,
      IsIsog u ∧ IsIsog w ∧ (∀ P, w (u P) = n • P) ∧ (∀ Q, u (w Q) = n • Q) ∧
      (∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (u P)) := by
  obtain ⟨W₁, hE, hW₁, σ, hσ⟩ := exists_velu_sigma (L := L) hNF f g hfg
  have := hE
  have hG : (Fintype.card (HT L N f) : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact card_HT_ne_zero hNF f
  have hFr := frob_mem_HT (L := L) (N := N) f
  obtain ⟨ψH, hψH, -, hd1, hd2, -⟩ := exists_dual hG hW₁ hFr
  obtain ⟨θ, hθ⟩ := exists_conj σ
  obtain ⟨θ', hθ'⟩ := exists_conj σ.symm
  have hγ : ∀ k, σ (sig W' (frobAut (F := F) L) k) = sig W₁ (frobAut (F := F) L) (σ k) :=
    sig_sigma f (frobAut (F := F) L) hW₁ (sig_qx hFr) (sig_qy hFr) σ hσ
  refine ⟨Fintype.card (HT L N f), fun h => hG ?_, θ.comp (qmap hG hW₁), ψH.comp θ',
    IsIsog.comp ⟨genPt σ, hasGenI_of_conj hθ⟩ ⟨qPt hW₁, hasGenI_qmap hG hW₁⟩,
    IsIsog.comp hψH ⟨genPt σ.symm, hasGenI_of_conj hθ'⟩, fun P => ?_, fun Q => ?_, fun P => ?_⟩
  · rw [← map_natCast (algebraMap F L), h, map_zero]
  · show ψH (θ' (θ (qmap hG hW₁ P))) = _
    rw [conj_inv hθ hθ', hd1]
  · show θ (qmap hG hW₁ (ψH (θ' Q))) = _
    rw [hd2, map_nsmul, conj_inv' hθ hθ']
  · show θ (qmap hG hW₁ (RPLib.EllFq.frob W L P)) = RPLib.EllFq.frob W' L (θ (qmap hG hW₁ P))
    rw [qmap_frob hG hW₁ hFr, conj_frob' hθ hγ]

end Data

end RPLib.DWS


