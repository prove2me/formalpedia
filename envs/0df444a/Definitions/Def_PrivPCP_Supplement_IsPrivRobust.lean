-- Prove2me | Definitions.Def_PrivPCP_Supplement_IsPrivRobust
-- name    : PrivPCP_Supplement_IsPrivRobust
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:55:48.99452+00:00
-- url     : https://prove2.me/theorems/ed051c7e-8642-4ce3-b6e7-fca05c64f797
-- title:
--   Private and robust circuits with auxiliary proofs (Definition 5.3)
-- statement:
--   Let $f:X\to\{0,1\}\subseteq\mathbb F_q$, and let a randomized encoding of $x\in X$ have law $\mathcal C_x$ and set of values $\mathrm{Enc}(x)\subseteq\mathbb F_q^{N_0}$, so that the underlying code is $\mathcal C_{\mathrm{in}}=\bigcup_x\mathrm{Enc}(x)$. A circuit $C$ with tester $T$, honest prover $P$ and prescribed random-word laws $R$ (the same for every $x$) is a **private, robust circuit for $f$** with fan-in $\Delta$, layerwise privacy $\delta$, joint privacy $\nu$ and robustness parameters $(\gamma,\epsilon_{\mathrm{in}},\epsilon_{\mathrm{lay}})$ if $C$ and $T$ are well formed, every gate has fan-in at most $\Delta$, the tester queries at most $\Delta$ wires for every fixing of its randomness, and:
--
--   1. **Honest correctness.** For every $x$ and every outcome of the honest execution with $W_0\sim\mathcal C_x$, the tester accepts with probability one and $W_L=f(x)$.
--   2. **Privacy.** In the honest execution:
--      (a) for every layer and every set $U$ of fewer than a $\delta$-fraction of the coordinates of its full input block $(W_{\ell-1},\Pi_\ell,R_\ell)$, the law of the values on $U$ does not depend on $x$;
--      (b) for all $x,x'$ and every set $U$ of transcript coordinates with $\mu(U)<\nu$, $\mathrm{Tr}_C(x)|_U\overset{d}{=}\mathrm{Tr}_C(x')|_U$, where $\mu$ is the measure of §6.3.
--   3. **Robustness.** For every $\epsilon_{\mathrm{lay}}$-faulty execution, with arbitrary input, auxiliary and random words:
--      (a) if $\Pr[T\text{ rejects}]\le\gamma$, then $\mathrm{dist}(W_0,\mathcal C_{\mathrm{in}})\le\epsilon_{\mathrm{in}}N_0$;
--      (b) for every $x$ with $\mathrm{dist}(W_0,\mathrm{Enc}(x))\le\epsilon_{\mathrm{in}}N_0$, if $\Pr[T\text{ rejects}]\le\gamma$, then $W_L=f(x)$.
--
--   Here $\mathrm{dist}$ is Hamming distance. This is the guarantee Theorem 5.5 provides for the zero-on-subcube function, and the object the private PCP of Section 8 is built from.
--
--   **Formalization Note** $\mathrm{dist}(w,S)\le r$ is written as the existence of $c\in S$ at Hamming distance at most $r$ (the distance to a finite set is a minimum). Clause 3(a) is required for every $\epsilon_{\mathrm{lay}}$-faulty execution, fault-free ones included, the form in which Lemma 7.1 proves it. The honest prover and the random-word laws are part of the construction ("The construction specifies their honest distributions"), and honest correctness holds with these prescribed laws.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 5.3, pp.27–28 (PDF pp.29–30); Definition 5.2, p.27; §6.3, p.39; Lemma 7.1, p.40

import Mathlib
import Definitions.Def_PrivPCP_Supplement_LCircuit_honestLaw
import Definitions.Def_PrivPCP_Supplement_circuitMu

set_option autoImplicit false

namespace PrivPCP.Supplement

/-- **Definition 5.3 (Private & Robust Circuit with Auxiliary Proofs)** (Bafna, Vyas, *Private PCPs
from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Definition 5.3,
pp.27–28, with Definition 5.2, p.27, and the measure `µ` of §6.3, p.39). Let `f : X → 𝔽_q` (values
`0, 1`) and let the randomized encoding of `x ∈ X` have law `encLaw x` (the law `C_x` of `Enc(x; r)`)
and support set `encSet x` (`Enc(x)`), so that `C_in = ⋃_x Enc(x)`. The circuit `C` with tester `T`,
honest prover `P` (the prescribed laws of the auxiliary words) and prescribed random-word laws `R`
(the honest distributions of the random words, the same for every `x`) is a **private, robust circuit for
`f`** with fan-in `Δ`, layerwise privacy `δ`, joint privacy `ν` under `µ`, and robustness parameters
`(γ, ε_in, ε_lay)` if `C` and `T` are well formed, every gate has fan-in at most `Δ`, the tester
queries at most `Δ` wires for every fixing of its randomness, and:
1. **Honest correctness.** For every `x`, in every outcome of the honest execution with
   `W_0 ∼ C_x` (auxiliary words from `P x`, random words from `R`), the tester accepts with probability one and `W_L = f(x)`.
2. **Privacy.** In the honest execution:
   (a) for every layer `ℓ`, every set `U` of coordinates of the full input block
   `(W_{ℓ−1}, Π_ℓ, R_ℓ)` with `|U| < δ · |block|` has the same law of values for every `x`
   (**`δ`-layerwise privacy**);
   (b) for all `x, x′` and every set `U` of transcript coordinates with `µ(U) < ν`,
   `Tr_C(x)|_U` and `Tr_C(x′)|_U` have the same law (**`ν`-joint privacy under `µ`**).
3. **Robustness.** For every transcript `t` (arbitrary input, arbitrary auxiliary and random words)
   that is an `ε_lay`-faulty execution (fewer than an `ε_lay`-fraction of the gates of each layer
   output arbitrary values, all others evaluate correctly on their actual inputs):
   (a) if `Pr[T rejects] ⩽ γ`, then `dist(W_0, C_in) ⩽ ε_in N₀`;
   (b) for every `x` with `dist(W_0, Enc(x)) ⩽ ε_in N₀`, if `Pr[T rejects] ⩽ γ`, then `W_L = f(x)`.

**Formalization Note** `dist(w, S) ⩽ r` is written `∃ c ∈ S, hammingDist w c ⩽ r`, the Hamming
distance to a finite set being a minimum. Clause 3(a) is required for every `ε_lay`-faulty execution
(fault-free ones included), the form in which Lemma 7.1 (p.40) proves it. The honest prover is part of
the construction ("The construction specifies their honest distributions", p.27), and honest
correctness holds with these prescribed laws. The prover is causal by the form of `honestLaw` (at
layer `ℓ` it sees only the input and the earlier layers). Laws of the values on a set `U` are images of the
transcript law under restriction to `U`. -/
def IsPrivRobust {q : ℕ} [NeZero q] {X : Type} (C : LCircuit) (T : LTester)
    (R : (ℓ : Fin C.L) → PMF (Fin (C.layer ℓ).rndLen → ZMod q))
    (P : X → Fin C.L → (C.Coord → ZMod q) → PMF (C.AuxIdx → ZMod q))
    (f : X → ZMod q) (encLaw : X → PMF (Fin C.N0 → ZMod q))
    (encSet : X → Set (Fin C.N0 → ZMod q)) (Δ δ ν γ εin εlay : ℝ) : Prop :=
  C.WF ∧ T.WF C ∧
  (∀ o : C.OutIdx, ((C.gate o).ins.length : ℝ) ≤ Δ) ∧
  (∀ e ∈ T.tests, 0 < e.weight → (e.queries.length : ℝ) ≤ Δ) ∧
  -- 1. honest correctness
  (∀ x, ∀ t ∈ (C.honestLaw (encLaw x) R (P x)).support, T.rejProb C t = 0 ∧ C.outVal t = f x) ∧
  -- 2(a). δ-layerwise privacy
  (∀ (x x' : X) (ℓ : Fin C.L) (U : Set C.Coord), U ⊆ C.blockSet ℓ →
    (U.ncard : ℝ) < δ * (C.blockSet ℓ).ncard →
    (C.honestLaw (encLaw x) R (P x)).map (fun t (c : U) => t c) =
      (C.honestLaw (encLaw x') R (P x')).map (fun t (c : U) => t c)) ∧
  -- 2(b). ν-joint privacy under µ
  (∀ (x x' : X) (U : Set C.Coord), circuitMu C T U < ν →
    (C.honestLaw (encLaw x) R (P x)).map (fun t (c : U) => t c) =
      (C.honestLaw (encLaw x') R (P x')).map (fun t (c : U) => t c)) ∧
  -- 3(a). robustness: low rejection puts the input near the code
  (∀ (t : C.Coord → ZMod q) (E : Set C.OutIdx), C.FewFaults εlay E → C.Computes E t →
    T.rejProb C t ≤ γ →
    ∃ c ∈ ⋃ x, encSet x, (hammingDist (fun j => t (Sum.inl j)) c : ℝ) ≤ εin * C.N0) ∧
  -- 3(b). robustness: low rejection near `Enc(x)` gives the right output
  (∀ (x : X) (t : C.Coord → ZMod q) (E : Set C.OutIdx),
    (∃ c ∈ encSet x, (hammingDist (fun j => t (Sum.inl j)) c : ℝ) ≤ εin * C.N0) →
    C.FewFaults εlay E → C.Computes E t → T.rejProb C t ≤ γ → C.outVal t = f x)

end PrivPCP.Supplement


