-- Prove2me | Definitions.Def_HypRecov_SketchGuarantee
-- name    : HypRecov_SketchGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:06.641348+00:00
-- url     : https://prove2.me/theorems/6489f777-04ce-41e3-a9f3-e12b797d81c8
-- title:
--   The guarantee of a randomized one-pass linear sketch
-- statement:
--   A **linear sketch** consists of four Turing machines, an initializer, an update machine, a subtraction machine and a decoder, together with coin sizes $N,M$ depending on $(n,r,k,m)$; the coins $\omega$ are uniform on $\{0,\dots,M-1\}^N$.
--
--   Given constants $C,c$, a size $w$, a failure budget $\eta$ and an order $q$, write $m=\lceil 1/\eta\rceil$,
--   $$S=\big\lfloor C\,w\,(1+\log_2(w/\eta))^c\big\rfloor,\qquad T_\ell=\big\lfloor C\,\big(w(1+\log_2(1/\eta))(1+\ell)\big)^c\big\rfloor .$$
--   The sketch **satisfies the guarantee** if $M\ge 1$ and there is a state function $\mathrm{sk}(\omega,y)$ of the coins and the net count vector $y$ such that for every $\omega$:
--
--   1. every state has at most $S$ bits;
--   2. the initializer turns the coins into $\mathrm{sk}(\omega,0)$ within $T_0$ steps and space $S$;
--   3. for every $y$, every $q$-set $A$ and every $\Delta\in\mathbb Z$, the update machine turns $(\mathrm{sk}(\omega,y),A,\Delta)$ into $\mathrm{sk}(\omega,y+\Delta\mathbf 1_A)$ within $T_\ell$ steps, $\ell$ the bit length of $\Delta$, and space $S$ plus its input;
--   4. the subtraction machine turns $(\mathrm{sk}(\omega,y),\mathrm{sk}(\omega,y'))$ into $\mathrm{sk}(\omega,y-y')$ within $T_0$ steps and space $S$ plus its input;
--   5. the decoder halts on every state $\mathrm{sk}(\omega,y)$ within $T_0$ steps and space $S$;
--
--   and for every simple $r$-uniform $H$ and every valid $q$-projection stream $\sigma$ of $H$, fixed before the coins,
--   $$\Pr_\omega\big[\text{the decoder on }\mathrm{sk}(\omega,\mathrm{net}_\sigma)\text{ does not output a correct answer}\big]\le\eta .$$
--
--   Items 1–4 are the reading of "one-pass linear sketch": the state depends on the stream only through its net counts, so it is the same for every ordering; updates are additive; two states can be subtracted, as the paper does in Algorithm 2 and Theorem 9.1. The space budget charges the random description, the state, the decoding workspace and the output.
--
--   **Formalization Note** $S$ is the form of $O(w\,\mathrm{polylog}(w/\eta))$ and $T_\ell$ of "time polynomial in $n,r,k,\log(1/\eta)$" (and in the increment's bit length), with absolute constants $C,c$. The decoder's bounds hold on every state, valid or not.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3); Theorem 6.4, pp.15–16; Theorem D.1, p.37

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_HypRecov_SpaceWithin
import Definitions.Def_HypRecov_encInit
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_HypRecov_IsValidStream

namespace HypRecov

/-- **A randomized one-pass linear sketch: four machines and a coin space.** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Theorem 1.1, p.2 (PDF p.3).

`init` builds the initial state from the coins, `upd` applies one fragment update, `sub` subtracts
two states, `dec` decodes. The coins are uniform on `Fin N → Fin M`, where `N` and `M` depend on
`n, r, k` and `m = ⌈1/η⌉₊`. -/
structure LinearSketch where
  init : Turing.TM2ComputableAux Bool Bool
  upd : Turing.TM2ComputableAux Bool Bool
  sub : Turing.TM2ComputableAux Bool Bool
  dec : Turing.TM2ComputableAux Bool Bool
  N : ℕ → ℕ → ℕ → ℕ → ℕ
  M : ℕ → ℕ → ℕ → ℕ → ℕ

/-- The space budget `C·w·(1 + log₂(w/η))^c`, the form of `O(w polylog(w/η))` with absolute
constants `C, c` (Theorem 1.1, p.2: `w = nrk`; Theorem D.1, p.37: `w = nr`). -/
noncomputable def spaceBudget (C c w : ℕ) (η : ℝ) : ℕ :=
  ⌊(C : ℝ) * w * (1 + Real.logb 2 (w / η)) ^ c⌋₊

/-- The time budget `C·(w·(1 + log₂(1/η))·(1 + ℓ))^c`, the form of "time polynomial in n, r, k,
log(1/η)" (Theorem 1.1, p.2); `ℓ` is the bit length of an update's increment and `0` otherwise. -/
noncomputable def timeBudget (C c w : ℕ) (η : ℝ) (ℓ : ℕ) : ℕ :=
  ⌊(C : ℝ) * ((w : ℝ) * (1 + Real.logb 2 (1 / η)) * (1 + (ℓ : ℝ))) ^ c⌋₊

/-- **The guarantee of a one-pass linear sketch at order `q`.** Zhang, Chen, Shen, *Hypergraph
Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…),
Theorem 1.1, p.2 (PDF p.3): "There is a randomized one-pass linear sketch of an anonymous
q_id-projection stream that recovers ℬ_k(H) with probability at least 1 − η. Its total working space,
including random descriptions and decoding workspace, is O(nrk polylog(nrk/η)) bits. Preprocessing,
per-fragment update and decoding take time polynomial in n, r, k, log(1/η). Update time also accounts
for the supplied increment's bit length. … The guarantee holds for each fixed input stream,
independently of its ordering. The stream is independent of the sketch coins." Also Theorem 6.4,
p.15, and Theorem D.1, p.37.

`SketchGuarantee A C c n r k w η q Correct` holds when, with `m = ⌈1/η⌉₊`, `S = spaceBudget C c w η`,
`T = timeBudget C c w η 0`, the coin alphabet is nonempty and there is a state function `sk ω y`
(coins `ω`, net count vector `y`) such that for every coin value `ω`:
1. every state has at most `S` bits;
2. `init` maps the coins to `sk ω 0` within `T` steps and space `S` (coins included);
3. `upd` maps `(sk ω y, A, Δ)`, `|A| = q`, to `sk ω (y + Δ·1_A)` within
   `timeBudget C c w η (bit length of Δ)` steps and space `S` plus the input length;
4. `sub` maps `(sk ω y, sk ω y')` to `sk ω (y − y')` within `T` steps and space `S` plus input;
5. `dec` halts on every state `sk ω y` within `T` steps and space `S` (output included);

and for every `r`-uniform `H` on `Fin n` and every valid `q`-projection stream `σ` of `H`, the
fraction of coins for which `dec` on `sk ω (net σ)` fails to output a `Correct` answer is at most `η`.

**Formalization Note.** "Linear sketch" is read as items 1–5: the state is a function of the coins
and of the net count vector, so it does not depend on the order of the updates, an update adds
`Δ·1_A`, and two states can be subtracted. Only `init` reads the coins, and its input is charged to
its space, so the random description counts. The stream is quantified before the coins. Space counts
all stacks (`SpaceWithin`); the update and subtraction machines may in addition hold their input. -/
def SketchGuarantee (A : LinearSketch) (C c n r k w : ℕ) (η : ℝ) (q : ℕ)
    (Correct : Finset (Finset (Fin n)) → List Bool → Prop) : Prop :=
  1 ≤ A.M n r k ⌈1 / η⌉₊ ∧
  ∃ sk : (Fin (A.N n r k ⌈1 / η⌉₊) → Fin (A.M n r k ⌈1 / η⌉₊)) → (Finset (Fin n) → ℤ) → List Bool,
    (∀ ω,
      (∀ y, (sk ω y).length ≤ spaceBudget C c w η) ∧
      SpikyCVP.RunsWithin A.init (encInit n r k ⌈1 / η⌉₊ (coinList ω)) (sk ω 0) (timeBudget C c w η 0) ∧
      SpaceWithin A.init (encInit n r k ⌈1 / η⌉₊ (coinList ω)) (spaceBudget C c w η) ∧
      (∀ (y : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (Δ : ℤ), B.card = q →
        SpikyCVP.RunsWithin A.upd (encUpd r k ⌈1 / η⌉₊ (sk ω y) B Δ) (sk ω (y + Pi.single B Δ))
            (timeBudget C c w η (Nat.size Δ.natAbs)) ∧
          SpaceWithin A.upd (encUpd r k ⌈1 / η⌉₊ (sk ω y) B Δ)
            (spaceBudget C c w η + (encUpd r k ⌈1 / η⌉₊ (sk ω y) B Δ).length)) ∧
      (∀ y y' : Finset (Fin n) → ℤ,
        SpikyCVP.RunsWithin A.sub (encSub n r k ⌈1 / η⌉₊ (sk ω y) (sk ω y')) (sk ω (y - y'))
            (timeBudget C c w η 0) ∧
          SpaceWithin A.sub (encSub n r k ⌈1 / η⌉₊ (sk ω y) (sk ω y'))
            (spaceBudget C c w η + (encSub n r k ⌈1 / η⌉₊ (sk ω y) (sk ω y')).length)) ∧
      (∀ y : Finset (Fin n) → ℤ, ∃ out : List Bool,
        SpikyCVP.RunsWithin A.dec (encDec n r k ⌈1 / η⌉₊ (sk ω y)) out (timeBudget C c w η 0) ∧
          SpaceWithin A.dec (encDec n r k ⌈1 / η⌉₊ (sk ω y)) (spaceBudget C c w η))) ∧
    ∀ (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = r) →
      ∀ σ : List (Finset (Fin n) × ℤ), IsValidStream E q σ →
        PunctSketch.coinProb (fun ω : Fin (A.N n r k ⌈1 / η⌉₊) → Fin (A.M n r k ⌈1 / η⌉₊) =>
          ¬ ∃ out : List Bool,
            SpikyCVP.RunsWithin A.dec (encDec n r k ⌈1 / η⌉₊ (sk ω (net σ))) out (timeBudget C c w η 0) ∧
              Correct E out) ≤ η

end HypRecov


