-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_Extension
-- name    : DenseProdQSAT_Testing_Extension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:15.339565+00:00
-- url     : https://prove2.me/theorems/1275defb-63bb-40a7-a6ce-9136e71da057
-- title:
--   Extension spaces, historical potentials and exact bad sets
-- statement:
--   Fix an instance $\Phi$, a local assignment $A=(F,\psi)$, and $X\subseteq V\setminus F$ with $1\le|X|\le k-1$. The extension space $L_A(X)$ is the complex subspace of vectors $u\in\mathcal H_X$ such that $\Pi_S(u\otimes\psi_{S\setminus X})=0$ for every $X\subseteq S\subseteq F\cup X$ with $|S|\le k$. Tensoring with the nonzero assigned factors outside $S$ gives exactly the paper's full-space condition. Vectors in this subspace need not be normalized.
--
--   $$W_A=\sum_{\substack{X\subseteq V\setminus F\\1\le|X|\le k-1}}n^{k-|X|-1}\dim_{\mathbb C}L_A(X),\qquad\Delta_A(x,v)=W_A-W_{A(x,v)}.$$
--
--   Write $J=\lceil\log_2(16/\varepsilon)\rceil$ and $\tau_i=2^{-i}$. The exact bad set $R_i(A)$ contains the unassigned $y$ for which every prefix time and every compatible unit insertion has drop at least $\tau_i n^{k-1}$. Empty compatible unit spheres give vacuous universal conditions. Prefixes include time zero, and appended states overwrite only the new coordinate. No potential bound or density conclusion is an instance field. The machinery is used with $k\ge2$, positive $n,d$, and $0<\varepsilon\le1$.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Definition 2.1, Definition 2.3, Eq. (1), Definition 2.5 p. 6, p. 5

import Definitions.Def_DenseProdQSAT_Testing_Model
set_option autoImplicit false

namespace DenseProdQSAT.Testing

/-- Tensor an unknown vector on X with the assigned factors on S \ X. -/
noncomputable def MixedTensor {n d : ℕ} (X S : Finset (Fin n)) (hXS : X ⊆ S)
    (ψ : States n d) : QVector d X →ₗ[ℂ] QVector d S where
  toFun u a := u (fun x => a ⟨x.val, hXS x.property⟩) *
    ∏ z : ↥(S \ X), ψ z (a ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩)
  map_add' u v := by
    ext a
    simp only [Pi.add_apply, add_mul]
  map_smul' c u := by
    ext a
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

noncomputable def ExtensionSpace {n k d : ℕ} (Φ : Instance n k d)
    (F X : Finset (Fin n)) (ψ : States n d) : Submodule ℂ (QVector d X) :=
  ⨅ (S : Supports n k) (hXS : X ⊆ S.val) (_hSF : S.val ⊆ F ∪ X),
    LinearMap.ker ((Matrix.toLin' (Φ.projector S)).comp (MixedTensor X S.val hXS ψ))

noncomputable def Potential {n k d : ℕ} (Φ : Instance n k d)
    (F : List (Fin n)) (ψ : States n d) : ℝ := by
  classical
  exact ∑ X ∈ (Finset.univ \ F.toFinset).powerset.filter
      (fun X => X.Nonempty ∧ X.card ≤ k - 1),
    (n : ℝ) ^ (k - X.card - 1) * Module.finrank ℂ (ExtensionSpace Φ F.toFinset X ψ)

noncomputable def ExactDrop {n k d : ℕ} (Φ : Instance n k d)
    (F : List (Fin n)) (ψ : States n d) (x : Fin n) (v : Fin d → ℂ) : ℝ :=
  Potential Φ F ψ - Potential Φ (F ++ [x]) (Function.update ψ x v)

noncomputable def ScaleCount (ε : ℝ) : ℕ := ⌈Real.log (16 / ε) / Real.log 2⌉₊
noncomputable def Tau (i : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ i

def Compatible {n k d : ℕ} (Φ : Instance n k d) (F : List (Fin n))
    (ψ : States n d) (x : Fin n) (v : Fin d → ℂ) : Prop :=
  UnitState v ∧ (fun a : Config d {x} => v (a ⟨x, Finset.mem_singleton_self x⟩)) ∈
    ExtensionSpace Φ F.toFinset {x} ψ

noncomputable def BadSet {n k d : ℕ} (Φ : Instance n k d)
    (F : List (Fin n)) (ψ : States n d) (i : ℕ) : Finset (Fin n) := by
  classical
  exact (Finset.univ \ F.toFinset).filter (fun y => ∀ t ≤ F.length,
    ∀ v : Fin d → ℂ, Compatible Φ (F.take t) ψ y v →
      Tau i * (n : ℝ) ^ (k - 1) ≤ ExactDrop Φ (F.take t) ψ y v)

end DenseProdQSAT.Testing


