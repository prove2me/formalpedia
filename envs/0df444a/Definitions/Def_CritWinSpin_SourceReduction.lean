-- Prove2me | Definitions.Def_CritWinSpin_SourceReduction
-- name    : CritWinSpin_SourceReduction
-- status  : Definition
-- author  : @Maxliu
-- created : 2026-11-17T11:23:42.76175+00:00
-- url     : https://prove2.me/theorems/377ccc98-4f61-4609-85d1-cf2539e78973
-- title:
--   Waters 源证明的分解接口：电路记录、解析性质、CDH 归约和有效零场适配
-- statement:
--   把 Theorem 5.1 的可重用部分分别记为：验证电路的公开求值和签名恢复接口，源的几何及有效编码，统计性质 (i)--(ii)，随机公钥实验中的 CDH 归约，以及零场适配的多项式时间编码与随机包装器。
--
--   统计与密码部分分别保持原精度和损失：
--   $$\mathrm{TV}(\mu_P,V_P)\le e^{-n_0^2},\qquad
--   \Pr(\text{新消息伪造})\le C T\sqrt d\,\mathrm{Adv}_{\rm CDH}(B).$$
--   这些谓词只展开并分组原定义中的数据与结论，不引入任何定理或未经证明的公理。签名恢复接口明确要求从公钥和完整电路记录恢复原消息及两个群元素的公开编码。
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission, manuscript SHA256 f77584dab87d9e6d0936a083a2e3d26476a91a9d73dc303674514a3257c0de95; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/943.pdf; §§5.1--5.2, printed pp.18--20, Theorem 5.1, equations (26)--(27).

import Mathlib
import Definitions.Def_CritWinSpin_BinarySource

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

/-- Public forward evaluation and recovery of the input message/signature wires of a
verification circuit; the recovery map receives only the public key and full wire record.
The last clause is the regular honest-record injectivity used in Theorem 5.1(ii).
Source: Liu--Zhang--Ren, STOC 2027 submission, §§5.1--5.2, printed pp.18--20. -/
def SourceCircuitRecords {F : BilinearFamily} (circ : WatersCircuit F) : Prop :=
  PolyBounded circ.n0 ∧ (∀ d, d ^ 2 ≤ circ.n0 d) ∧
  (∃ evalF : Str → Str, CookPvsNP.PolyTimeComputable evalF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
      (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
      evalF (tupleCode [pkCode F d desc key, List.ofFn m, F.encG desc s₁, F.encG desc s₂]) =
        List.ofFn (circ.evalCfg d desc key m s₁ s₂)) ∧
  (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
    (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
    circ.psi d desc key (circ.evalCfg d desc key m s₁ s₂) = m) ∧
  (∃ recoverF : Str → Str, CookPvsNP.PolyTimeComputable recoverF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
      (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
      recoverF (tupleCode [pkCode F d desc key, List.ofFn (circ.evalCfg d desc key m s₁ s₂)]) =
        tupleCode [List.ofFn m, F.encG desc s₁, F.encG desc s₂]) ∧
  (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
    (m₁ m₂ : Fin d → Bool) (r₁ r₂ : Fin (F.q desc)),
    circ.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
      circ.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
    m₁ = m₂ ∧ r₁ = r₂)

/-- Polynomial row width, symmetry and zero diagonal of the source model. Source: Theorem 5.1, printed pp.19--20. -/
def SourceGeometry (F : BilinearFamily) (src : BinarySource F) : Prop :=
  (∃ w : ℕ, 1 ≤ w ∧ ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
    (src.ham d desc key).1.IsSymm ∧ (∀ i, (src.ham d desc key).1 i i = 0) ∧
    width (castM (src.ham d desc key).1) (castV (src.ham d desc key).2) ≤ ((src.n d : ℝ)) ^ w)

/-- Uniform polynomial-time public encodings of the source Hamiltonian and message map. Source: Theorem 5.1, printed pp.19--20. -/
def SourceEfficient (F : BilinearFamily) (src : BinarySource F) : Prop :=
  (∃ hamF : Str → Str, CookPvsNP.PolyTimeComputable hamF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      hamF (pkCode F d desc key) = encInst (src.ham d desc key)) ∧
  (∃ psiF : Str → Str, CookPvsNP.PolyTimeComputable psiF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d) (y : BinCfg (src.n d)),
      psiF (tupleCode [pkCode F d desc key, List.ofFn y]) = List.ofFn (src.psi d desc key y))

/-- Exactly the statistical clauses (i)--(ii) of SourceProps, with no cryptographic assumption. Source: Theorem 5.1, printed pp.19--20. -/
def SourceStatistics (F : BilinearFamily) (src : BinarySource F) : Prop :=
  (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
    let μ := muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)
    let V := unifOn (src.omega d desc key)
    let Ψ := src.psi d desc key
    -- (i)
    tvDist μ V ≤ Real.exp (-((src.n0 d : ℝ) ^ 2)) ∧
    (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
      (T : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2))) ∧
    -- (ii)
    (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
    (∀ (T : ℕ) (i : Fin T)
      (pred : ({j : Fin T // j ≠ i} → BinCfg (src.n d)) → (Fin d → Bool) → ℝ),
      (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
      ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
        1 / (2 : ℝ) ^ d) ∧
    (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs *
        (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
      (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)))

/-- Exactly the random-key CDH reduction clause (iii) of SourceProps. Source: Theorem 5.1, printed pp.19--20. -/
def SourceSecurity (F : BilinearFamily) (src : BinarySource F) (C : ℝ) : Prop :=
    (∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
    ∃ B : PPT, ∃ d₀ : ℕ, ∀ d ≥ d₀,
      forgeProb src A (T d) d ≤ C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d)

/-- Effective public descriptions of the zero-field model and message map, together
with the PPT adapter that adds independent signs to training records and decodes its output.
The pointwise probability inequality implies the key-generation-averaged inequality through
`p7b_5_1_zerofield_math`. Source: Theorem 5.1, proof, printed p.20, and (26), p.19. -/
def SourceHatEffective {F : BilinearFamily} (src : BinarySource F) : Prop :=
  (∃ hamF_hat : Str → Str, CookPvsNP.PolyTimeComputable hamF_hat ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      hamF_hat (pkCode F d desc key) = encInst ((hatSource src).ham d desc key)) ∧
  (∃ psiF_hat : Str → Str, CookPvsNP.PolyTimeComputable psiF_hat ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
      (y : BinCfg (src.n d + 1)),
      psiF_hat (tupleCode [pkCode F d desc key, List.ofFn y]) =
        List.ofFn ((hatSource src).psi d desc key y)) ∧
  (∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
    ∃ B_wrap : PPT, ∀ (d : ℕ) (desc : Str) (key : WatersKey F desc d)
      (Fs : Fin (T d) → BinCfg (src.n d)),
      (1 / (2 : ℝ) ^ (T d)) * ∑ ts : Fin (T d) → Bool,
        A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
            List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
          (fun s => ∃ y_hat : BinCfg (src.n d + 1), s = List.ofFn y_hat ∧
            hatProd y_hat ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key (hatProd y_hat) ≠ src.psi d desc key (Fs t)) ≤
        B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
          (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t)))

end CritWinSpin


