# Formalpedia

Formalized mathematics from [Prove2Me](https://prove2.me/formalpedia): theorems
and definitions stated in Lean 4, with the proofs accepted against them. This
snapshot was taken 2026-10-02 11:30 UTC and is refreshed daily.

## License

Everything in this repository is licensed under [Apache 2.0](LICENSE). Every
Lean file's header names its author and links to the original theorem or
submission on Prove2Me, and `index.jsonl` records the same.

Contributions made on Prove2Me since September 24, 2026 are included. Earlier
contributions appear once their author accepts the
[historical license agreement](https://prove2.me/terms#earlier-contributions).
Items that import work not yet licensed are left out until it is.

## Environments

| Directory | Mathlib | Toolchain | Theorems | Definitions | Solutions | Edges |
|---|---|---|---|---|---|---|
| `envs/0df444a` | `0df444a360ea` | leanprover/lean4:v4.33.1 | 61,582 | 18,405 | 57,913 | 389,241 |
| `envs/c5ea003` | `c5ea00351c28` | leanprover/lean4:v4.30.0 | 13,071 | 3,813 | 13,433 | 50,255 |
| `envs/777aaa6` | `777aaa61dcd2` | leanprover/lean4:v4.29.0-rc3 | 17,553 | 405 | 14,625 | 23,155 |

Each Lean environment is a separate directory. A theorem name is unique per
environment rather than globally, so the same name can carry a different status
under a different Mathlib revision.

## Layout

- `Theorems/Thm_<slug>.lean` -- the preamble and the statement. The proof is
  `sorry`: the file is the *statement*, and it is what a solution is checked
  against. `<slug>` is the theorem's Lean name with dots replaced by underscores.
- `Definitions/Def_<slug>.lean` -- definitions, importable by any theorem.
- `Solutions/Sol_<slug>.lean` -- an accepted proof, verbatim as verified, under
  a provenance header. Further proofs of the same theorem are `_2`, `_3`, and so
  on, in the order they were accepted.
- `index.jsonl` -- one JSON line per theorem: name, status, author, source, paths,
  and the sha256 of each solution as verified.
- `graph.jsonl` -- one JSON line per dependency edge, `{"parent", "child", "via"}`,
  read out of the `import` lines of the files above. `via` lists where the
  dependency appears: `statement` for the theorem's preamble, `solution` for a
  proof that introduces it, both when it appears in each.
- `MANIFEST.json` -- snapshot time, license, and per-environment Mathlib
  revision and counts.

A solution proves `theorem solution`, whose type the server checked to be
identical to the statement's. A solution marked `SKETCH_ACCEPTED` imports a
theorem that is still open.
