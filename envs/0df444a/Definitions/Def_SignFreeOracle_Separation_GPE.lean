-- Prove2me | Definitions.Def_SignFreeOracle_Separation_GPE
-- name    : SignFreeOracle_Separation_GPE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:22.247509+00:00
-- url     : https://prove2.me/theorems/10b63434-9a74-4c44-b051-41e8f31b9c0c
-- title:
--   The full sparse spectral promise and its uniform oracle-input verification
-- statement:
--   Fix known efficient spectral thresholds $a,b$, a polynomial degree bound $d$, and a positive polynomial $g$ with $a(m)-b(m)\ge1/g(m)$. Every simple labelled graph on $2^m$ vertices with maximum degree at most $d(m)$ is an instance, under the spectral promise
--   $$\mathrm{YES}:\lambda_{\max}(G)\ge a(m),\qquad \mathrm{NO}:\lambda_{\max}(G)\le b(m).$$
--   No extra assumption $0\le b<a\le d$ is imposed; empty promise regimes are retained. Oracle-input StoqMA membership requires one uniform restricted circuit family, one polynomial resource bound, and one efficient inverse-polynomially separated verification-threshold pair to work for every such graph and labelling. Completeness and soundness use the exact Boolean adjacency oracle and quantify over normalized complex witnesses. Efficient known thresholds spell out the computational input convention implicit in the complexity problem; graph membership is never supplied as a bit.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definition 3.2 and Proposition 3.4, pp. 9–10 (PDF pp. 9–10)

import Definitions.Def_SignFreeOracle_Separation_Encoding
import Definitions.Def_SignFreeOracle_Separation_StoqMA

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- Definition 3.2's fixed known degree and threshold data. There is no unannounced
0≤b<a≤d restriction: empty spectral YES/NO regimes retain their ordinary meaning. -/
structure GPEParameters where
  degreeBound : Polynomial ℕ
  a : ℕ → ℝ
  b : ℕ → ℝ
  gap : Polynomial ℕ
  aEfficient : EfficientThreshold a
  bEfficient : EfficientThreshold b
  gapPositive : ∀ m, 0 < gap.eval m
  separated : ∀ m, ((gap.eval m : ℕ) : ℝ)⁻¹ ≤ a m - b m

/-- Oracle-input StoqMA membership: one uniform circuit family and one pair of efficient
inverse-polynomially separated verification thresholds handle every sparse labelled graph.
The graph oracle is the instance, rather than a supplied YES/NO bit. -/
def GPEInStoqMA (P : GPEParameters) : Prop :=
  ∃ (C : ∀ m, StoqCircuit m) (a b : ℕ → ℝ) (gap size : Polynomial ℕ),
    UniformStoq C ∧ EfficientThreshold a ∧ EfficientThreshold b ∧
    (∀ m, 0 < gap.eval m ∧ (1 / 2 : ℝ) ≤ b m ∧ b m < a m ∧ a m ≤ 1 ∧
      ((gap.eval m : ℕ) : ℝ)⁻¹ ≤ a m - b m ∧
      m + (C m).witness + (C m).zeros + (C m).plus ≤ size.eval m ∧
      (C m).gates.length ≤ size.eval m) ∧
    ∀ (m : ℕ) (G : SimpleGraph (Fin (2 ^ m))) (π : Equiv.Perm (Fin (2 ^ m))),
      maxDegree G ≤ P.degreeBound.eval m →
      (P.a m ≤ perron G → ∃ ψ : QState (C m).witness, Normalized ψ ∧
        a m ≤ (C m).accept (graphBits (P.degreeBound.eval m) G π) (fun _ => false) ψ) ∧
      (perron G ≤ P.b m → ∀ ψ : QState (C m).witness, Normalized ψ →
        (C m).accept (graphBits (P.degreeBound.eval m) G π) (fun _ => false) ψ ≤ b m)

end SignFreeOracle.Separation


